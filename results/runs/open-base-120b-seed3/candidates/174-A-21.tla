---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\*-----------------------------------------------------------------
\* Constants required by the .cfg file
\*****************************************************************
CONSTANTS 
    Node,                 \* set of all node identifiers
    SlushLoopProcess,    \* set of loop process identifiers (one per node)
    SlushQueryProcess,   \* set of query process identifiers (one per node)
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* maximum number of iterations each loop performs
    SampleSetSize,       \* size of the random peer sample
    PickFlipThreshold,   \* number of equal‑colored replies needed to flip
    NoColor,             \* special value meaning “uncolored”
    NoMessage            \* placeholder for “no message” (unused but required)

\*-----------------------------------------------------------------
\* Derived sets and record definitions
\*****************************************************************
ColorSet  == {"Red", "Blue"}

MessageType == {"query", "reply", "term"}

Message == [type  : MessageType,
            src   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            color : (ColorSet \cup {NoColor})]

\* Helper functions that extract the host relationships from HostMapping
\*****************************************************************
NodeOfLoop(lp)   == CHOOSE t \in HostMapping : t[2] = lp
NodeOfQuery(qp)  == CHOOSE t \in HostMapping : t[3] = qp
LoopOfNode(n)    == CHOOSE t \in HostMapping : t[1] = n
QueryOfNode(n)   == CHOOSE t \in HostMapping : t[1] = n

\* The set of all subsets of Node (excluding a given node) having exactly
\* SampleSetSize elements.
\*****************************************************************
SampleSet(node) == { s \subseteq Node \ {node} : Cardinality(s) = SampleSetSize }

\*-----------------------------------------------------------------
\* State variables
\*****************************************************************
VARIABLES 
    color,   \* [node -> (ColorSet \cup {NoColor})]
    msgs,    \* set of Message
    pc,      \* [proc -> Nat] program counters
    sample,  \* [loopProc -> SUBSET Node] current peer sample
    iter     \* [loopProc -> Nat] number of completed iterations

vars == <<color, msgs, pc, sample, iter>>

\*-----------------------------------------------------------------
\* Initial state
\*****************************************************************
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\*-----------------------------------------------------------------
\* Actions
\*****************************************************************

\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ pc["client"] = 0
        /\ \E c \in ColorSet :
               /\ color' = [color EXCEPT ![n] = c]
               /\ UNCHANGED <<msgs, pc, sample, iter>>

\* 2. Loop process waits until its host node has been colored
LoopRequireColor ==
    \E lp \in SlushLoopProcess :
        LET n == NodeOfLoop(lp) IN
        /\ pc[lp] = 0
        /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = 1]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* 3. Loop process chooses a sample and sends queries
LoopQuery ==
    \E lp \in SlushLoopProcess :
        LET n == NodeOfLoop(lp) IN
        /\ pc[lp] = 1
        /\ iter[lp] < SlushIterationCount
        /\ \E s \in SampleSet(n) :
            LET msgsOut == { [type |-> "query",
                             src  |-> lp,
                             dst  |-> QueryOfNode(m),
                             color|-> color[n]] : m \in s } IN
            /\ sample' = [sample EXCEPT ![lp] = s]
            /\ msgs'   = msgs \cup msgsOut
            /\ pc'     = [pc EXCEPT ![lp] = 2]
            /\ UNCHANGED <<color, iter>>

\* 4. Query process answers a received query (adopting color if uncolored)
QueryRespond ==
    \E qp \in SlushQueryProcess :
        LET n == NodeOfQuery(qp) IN
        \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst  = qp
            /\ LET srcLp == m.src IN
               /\ IF color[n] = NoColor
                     THEN color' = [color EXCEPT ![n] = m.color]
                     ELSE UNCHANGED color
               /\ msgs' = msgs \cup
                         { [type |-> "reply",
                            src  |-> qp,
                            dst  |-> srcLp,
                            color|-> IF color[n] = NoColor THEN m.color ELSE color[n]] }
               /\ UNCHANGED <<pc, sample, iter>>

\* 5. Loop process tallies replies and possibly flips its node's color
LoopTally ==
    \E lp \in SlushLoopProcess :
        LET n == NodeOfLoop(lp) IN
        /\ pc[lp] = 2
        /\ \A q \in sample[lp] :
               \E r \in msgs :
                  /\ r.type = "reply"
                  /\ r.dst  = lp
                  /\ r.src  = QueryOfNode(q)
        /\ LET reds  == Cardinality({ r \in msgs :
                                      /\ r.type = "reply"
                                      /\ r.dst  = lp
                                      /\ r.color = "Red" })
               blues == Cardinality({ r \in msgs :
                                      /\ r.type = "reply"
                                      /\ r.dst  = lp
                                      /\ r.color = "Blue" }) IN
           /\ IF reds >= PickFlipThreshold
                 THEN color' = [color EXCEPT ![n] = "Red"]
              ELSE IF blues >= PickFlipThreshold
                 THEN color' = [color EXCEPT ![n] = "Blue"]
              ELSE UNCHANGED color
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
        /\ pc' = [pc EXCEPT ![lp] = IF iter' [lp] < SlushIterationCount THEN 1 ELSE 3]
        /\ UNCHANGED msgs

\* 6. After finishing all iterations the loop process broadcasts termination
LoopTerminate ==
    \E lp \in SlushLoopProcess :
        /\ pc[lp] = 3
        /\ msgs' = msgs \cup
                  { [type |-> "term",
                     src  |-> lp,
                     dst  |-> "client",
                     color|-> NoColor] }
        /\ pc' = [pc EXCEPT ![lp] = 4]
        /\ UNCHANGED <<color, sample, iter>>

\* 7. Query processes exit when every loop has sent a termination message
QueryExit ==
    \E qp \in SlushQueryProcess :
        /\ pc[qp] = 0
        /\ \A lp \in SlushLoopProcess :
               \E t \in msgs :
                  /\ t.type = "term"
                  /\ t.src  = lp
        /\ pc' = [pc EXCEPT ![qp] = 1]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* Stuttering step
Stutter ==
    UNCHANGED vars

\* Overall next-state relation
Next == 
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopQuery
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit
    \/ Stutter

\*-----------------------------------------------------------------
\* Specification
\*****************************************************************
Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* Type invariant required by the .cfg file
\*****************************************************************
TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs  \subseteq Message
    /\ pc    \in [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat]
    /\ sample \in [lp \in SlushLoopProcess -> SUBSET Node]
    /\ iter   \in [lp \in SlushLoopProcess -> Nat]

====