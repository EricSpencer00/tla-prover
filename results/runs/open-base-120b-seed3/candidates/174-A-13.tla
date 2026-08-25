---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* --------------------------------------------------------------
\* CONSTANTS (to be instantiated in the .cfg file)
\* --------------------------------------------------------------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Size of the peer sample taken each round
    PickFlipThreshold,  \* Minimum count of a color needed to flip
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value for "no message" (unused but required)

\* --------------------------------------------------------------
\* DERIVED CONSTANTS
\* --------------------------------------------------------------
\* The set of all processes (loop, query and the client)
Process == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* The two possible colors (any distinct identifiers different from NoColor)
ColorVal == {"Red", "Blue"}

\* --------------------------------------------------------------
\* STATE VARIABLES
\* --------------------------------------------------------------
VARIABLES 
    color,          \* [node \in Node |-> NoColor \/ ColorVal]
    msgs,           \* Set of messages currently in flight
    pc,             \* [proc \in Process |-> PCState]
    sampleSet,      \* [lp \in SlushLoopProcess |-> SUBSET Node]  (nodes sampled this round)
    iterCount,      \* [lp \in SlushLoopProcess |-> Nat]          (iterations completed)
    tally           \* [lp \in SlushLoopProcess |-> [c \in ColorVal |-> Nat]] (replies seen)

\* --------------------------------------------------------------
\* MESSAGE DEFINITION
\* --------------------------------------------------------------
Message == 
    [type : {"query", "reply", "term"},
     src  : Process,
     dst  : Process,
     payload : UNION {NoMessage} \cup ColorVal]   \* payload is a color for query/reply, NoMessage for term

\* --------------------------------------------------------------
\* PROGRAM COUNTER STATES
\* --------------------------------------------------------------
PCState == 
    {"ClientAssign",                 \* client assigning colors
     "LoopWaitColor",                \* loop waiting for its node to be colored
     "LoopSample",                   \* loop choosing a sample and sending queries
     "LoopAwaitReplies",             \* loop waiting for replies
     "LoopCheckFlip",                \* loop evaluating replies and possibly flipping
     "LoopTerminate",                \* loop broadcasting termination
     "LoopDone",                     \* loop finished all iterations
     "QueryReplyLoop",               \* query process waiting for queries
     "QueryDone"}                    \* query process terminated

\* --------------------------------------------------------------
\* INITIAL STATE
\* --------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [proc \in Process |-> 
                IF proc = "Client" THEN "ClientAssign"
                ELSE IF proc \in SlushLoopProcess THEN "LoopWaitColor"
                ELSE "QueryReplyLoop"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]
    /\ tally = [lp \in SlushLoopProcess |-> [c \in ColorVal |-> 0]]

\* --------------------------------------------------------------
\* HELPER FUNCTIONS
\* --------------------------------------------------------------
\* Retrieve the node associated with a given loop or query process
NodeOfLoop(lp) == 
    LET t == { <<n, l, q>> \in HostMapping : l = lp } IN
    IF Cardinality(t) = 1 THEN CHOOSE <<n, _, _>> \in t : TRUE ELSE NoColor

NodeOfQuery(qp) == 
    LET t == { <<n, l, q>> \in HostMapping : q = qp } IN
    IF Cardinality(t) = 1 THEN CHOOSE <<n, _, _>> \in t : TRUE ELSE NoColor

\* The set of query processes that belong to a set of nodes
QueryProcs(S) == { qp \in SlushQueryProcess : NodeOfQuery(qp) \in S }

\* --------------------------------------------------------------
\* ACTIONS
\* --------------------------------------------------------------

\* -----------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
\* -----------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "ClientAssign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in ColorVal :
        LET n == CHOOSE n \in Node : color[n] = NoColor IN
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED << msgs, sampleSet, iterCount, tally >>
        /\ pc' = [pc EXCEPT !["Client"] = "ClientAssign"]
    /\ OTHER unchanged variables

\* -----------------------------------------------------------------
\* 2. Loop process waits until its node has a color
\* -----------------------------------------------------------------
LoopWaitColor ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "LoopWaitColor"
        /\ LET n == NodeOfLoop(lp) IN n # NoColor /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "LoopSample"]
    /\ UNCHANGED << color, msgs, sampleSet, iterCount, tally >>

\* -----------------------------------------------------------------
\* 3. Loop process samples peers and sends query messages
\* -----------------------------------------------------------------
LoopSample ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "LoopSample"
        /\ LET n == NodeOfLoop(lp) IN
           \* choose a sample of distinct other nodes
           \E S \subseteq (Node \ {n}) : 
                Cardinality(S) = SampleSetSize
            /\ LET qps == QueryProcs(S) IN
               /\ msgs' = msgs \cup { [type    |-> "query",
                                      src     |-> lp,
                                      dst     |-> qp,
                                      payload |-> color[n]] : qp \in qps ]
               /\ sampleSet' = [sampleSet EXCEPT ![lp] = S]
               /\ tally' = [tally EXCEPT ![lp] = [c \in ColorVal |-> 0]]
               /\ pc' = [pc EXCEPT ![lp] = "LoopAwaitReplies"]
    /\ UNCHANGED << color, iterCount >>

\* -----------------------------------------------------------------
\* 4. Query process receives a query, possibly adopts the color, and replies
\* -----------------------------------------------------------------
QueryRespond ==
    /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "QueryReplyLoop"
        /\ \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst = qp
            /\ LET n == NodeOfQuery(qp) IN
               LET newColor == 
                    IF color[n] = NoColor THEN m.payload ELSE color[n] IN
               /\ color' = [color EXCEPT ![n] = newColor]
               /\ msgs' = (msgs \ {m}) \cup 
                         { [type    |-> "reply",
                            src     |-> qp,
                            dst     |-> m.src,
                            payload |-> newColor] }
               /\ pc' = [pc EXCEPT ![qp] = "QueryReplyLoop"]
    /\ UNCHANGED << sampleSet, iterCount, tally >>

\* -----------------------------------------------------------------
\* 5. Loop process receives a reply and updates its tally
\* -----------------------------------------------------------------
LoopReceiveReply ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "LoopAwaitReplies"
        /\ \E m \in msgs :
            /\ m.type = "reply"
            /\ m.dst = lp
            /\ LET c == m.payload IN
               /\ tally' = [tally EXCEPT ![lp][c] = @ + 1]
               /\ msgs' = msgs \ {m}
               /\ \* If all expected replies have been seen, move to check phase
                  IF /\ \A n \in sampleSet[lp] :
                        \E qp \in SlushQueryProcess :
                            NodeOfQuery(qp) = n /\ 
                            \E r \in msgs :
                                r.type = "reply" /\ r.dst = lp /\ r.payload \in ColorVal => FALSE
                     THEN pc' = [pc EXCEPT ![lp] = "LoopCheckFlip"]
                     ELSE pc' = pc
    /\ UNCHANGED << color, sampleSet, iterCount >>

\* -----------------------------------------------------------------
\* 6. Loop process checks tallies, possibly flips its node's color,
\*    increments iteration counter and decides next step
\* -----------------------------------------------------------------
LoopCheckFlip ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "LoopCheckFlip"
        /\ LET n == NodeOfLoop(lp) IN
           LET maxColor == 
                IF tally[lp]["Red"] >= PickFlipThreshold THEN "Red"
                ELSE IF tally[lp]["Blue"] >= PickFlipThreshold THEN "Blue"
                ELSE color[n] IN
           /\ color' = [color EXCEPT ![n] = maxColor]
           /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
           /\ IF iterCount'[lp] = SlushIterationCount
                THEN pc' = [pc EXCEPT ![lp] = "LoopTerminate"]
                ELSE pc' = [pc EXCEPT ![lp] = "LoopSample"]
           /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
           /\ tally' = [tally EXCEPT ![lp] = [c \in ColorVal |-> 0]]
    /\ UNCHANGED msgs

\* -----------------------------------------------------------------
\* 7. Loop process broadcasts termination message
\* -----------------------------------------------------------------
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "LoopTerminate"
        /\ msgs' = msgs \cup { [type    |-> "term",
                               src     |-> lp,
                               dst     |-> qp,
                               payload |-> NoMessage] 
                               : qp \in SlushQueryProcess }
        /\ pc' = [pc EXCEPT ![lp] = "LoopDone"]
    /\ UNCHANGED << color, sampleSet, iterCount, tally >>

\* -----------------------------------------------------------------
\* 8. Query processes exit when all termination messages have been received
\* -----------------------------------------------------------------
QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "QueryReplyLoop"
        /\ \A lp \in SlushLoopProcess :
              [type   |-> "term",
               src    |-> lp,
               dst    |-> qp,
               payload|-> NoMessage] \in msgs
        /\ pc' = [pc EXCEPT ![qp] = "QueryDone"]
    /\ UNCHANGED << color, msgs, sampleSet, iterCount, tally >>

\* -----------------------------------------------------------------
\* 9. No-op (stutter) step
\* -----------------------------------------------------------------
Stutter ==
    /\ UNCHANGED << color, msgs, pc, sampleSet, iterCount, tally >>

\* --------------------------------------------------------------
\* COMBINED NEXT ACTION
\* --------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopWaitColor
    \/ LoopSample
    \/ QueryRespond
    \/ LoopReceiveReply
    \/ LoopCheckFlip
    \/ LoopTerminate
    \/ QueryLoopExit
    \/ Stutter

\* --------------------------------------------------------------
\* SPECIFICATION
\* --------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sampleSet, iterCount, tally>>

\* --------------------------------------------------------------
\* TYPE INVARIANT
\* --------------------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : color[n] \in ColorVal \/ color[n] = NoColor
    /\ \A m \in msgs :
          /\ m.type \in {"query","reply","term"}
          /\ m.src \in Process
          /\ m.dst \in Process
          /\ IF m.type = "term" THEN m.payload = NoMessage
             ELSE m.payload \in ColorVal

\* --------------------------------------------------------------
\* THEOREM (the spec satisfies the invariant)
\* --------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====