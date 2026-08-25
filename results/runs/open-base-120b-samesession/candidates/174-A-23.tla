---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* one loop process per node
    SlushQueryProcess,   \* one query process per node
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* number of iterations each loop performs
    SampleSetSize,       \* size of the sampled peer set
    PickFlipThreshold,   \* threshold to flip color
    NoColor,             \* special value meaning "uncolored"
    NoMessage            \* placeholder for messages without payload

(***************************************************************************)
\*--- Derived sets ---------------------------------------------------------
\* The set of all processes (loop, query and the client)
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* Colors used by the protocol
ColorSet == {"Red", "Blue"}

\* Type of messages exchanged in the system
Message == [type : {"query", "reply", "term"},
            src  : Proc,
            dst  : Proc,
            col  : ColorSet \cup {NoColor}]

\* The set of possible program‑counter values
PCValues == {"Assign", "WaitColor", "Sample", "WaitReplies",
            "Terminate", "Done", "ReplyLoop"}

(***************************************************************************)
\*--- Variables -------------------------------------------------------------
VARIABLES
    color,   \* [node \in Node |-> NoColor \cup ColorSet]
    msgs,    \* set of in‑flight Message records
    pc,      \* [proc \in Proc |-> PCValues]
    sample,  \* [lp \in SlushLoopProcess |-> SUBSET SlushQueryProcess]
    iter     \* [lp \in SlushLoopProcess |-> Nat]

(***************************************************************************)
\*--- Helper definitions ----------------------------------------------------
\* Choose an arbitrary subset of S of exact cardinality k
ChooseSubset(S, k) == { T \in SUBSET S : Cardinality(T) = k }

\* Given a loop process lp, retrieve the node it hosts
HostNode(lp) == CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

\* Given a query process qp, retrieve the node it hosts
HostNodeFromQuery(qp) == CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

(***************************************************************************)
\*--- Initial state ---------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc     = [p \in Proc |
                    IF p = "Client"       THEN "Assign"
                    ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                    ELSE "ReplyLoop"]

(***************************************************************************)
\*--- Actions ---------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in ColorSet :
         LET n == CHOOSE n \in Node : color[n] = NoColor IN
         /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, sample, iter, pc>>

\* 2. Loop process waits until its host node is colored
LoopRequireColor(lp) ==
    /\ pc[lp] = "WaitColor"
    /\ LET n == HostNode(lp) IN
       /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* 3. Loop process samples peers and sends query messages
LoopSample(lp) ==
    /\ pc[lp] = "Sample"
    /\ LET n == HostNode(lp) IN
       newSample == ChooseSubset(SlushQueryProcess \ {lp}, SampleSetSize)
    /\ sample' = [sample EXCEPT ![lp] = newSample]
    /\ msgs'   = msgs \cup
                 { [type |-> "query",
                    src  |-> lp,
                    dst  |-> q,
                    col  |-> color[n]] : q \in newSample }
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<color, iter>>

\* 4. Query process replies to a received query (adopting the color if uncolored)
QueryRespond(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \E m \in msgs : m.type = "query" /\ m.dst = qp
    /\ LET m   == CHOOSE m \in msgs : m.type = "query" /\ m.dst = qp
           n   == HostNodeFromQuery(qp)
           newColor == IF color[n] = NoColor THEN m.col ELSE color[n]
           reply == [type |-> "reply",
                     src  |-> qp,
                     dst  |-> m.src,
                     col  |-> newColor]
       IN
       /\ color' = [color EXCEPT ![n] = newColor]
       /\ msgs'   = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<sample, iter, pc>>

\* 5. Loop process tallies replies and possibly flips its color
LoopTally(lp) ==
    /\ pc[lp] = "WaitReplies"
    /\ \A q \in sample[lp] :
         \E m \in msgs : m.type = "reply" /\ m.dst = lp /\ m.src = q
    /\ LET n == HostNode(lp) IN
       replies  == { m.col : m \in msgs :
                        m.type = "reply" /\ m.dst = lp /\ m.src \in sample[lp] }
       redCnt   == Cardinality({c \in replies : c = "Red"})
       blueCnt  == Cardinality({c \in replies : c = "Blue"})
       newCol   == IF redCnt >= PickFlipThreshold THEN "Red"
                  ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                  ELSE color[n]
       msgsDel  == { m \in msgs :
                        m.type = "reply" /\ m.dst = lp /\ m.src \in sample[lp] }
       inIter   == iter[lp] + 1
    /\ color' = [color EXCEPT ![n] = newCol]
    /\ msgs'   = msgs \ msgsDel
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iter'   = [iter EXCEPT ![lp] = inIter]
    /\ pc' = [pc EXCEPT ![lp] =
                IF inIter = SlushIterationCount
                   THEN "Terminate"
                   ELSE "Sample"]
    /\ UNCHANGED <<pc>>

\* 6. Loop process broadcasts termination
LoopTerminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ LET termMsg == [type |-> "term",
                       src  |-> lp,
                       dst  |-> "Client",
                       col  |-> NoMessage]
       IN
       /\ msgs' = msgs \cup {termMsg}
       /\ pc'   = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

\* 7. Query process exits once termination messages have been observed
QueryExit(qp) ==
    /\ pc[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess :
         \E m \in msgs : m.type = "term" /\ m.dst = "Client"
    /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\*--- Next-state relation ---------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : LoopRequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ ClientAssign

(***************************************************************************)
\*--- Specification ---------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

(***************************************************************************)
\*--- Invariant -------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs  \subseteq Message
    /\ pc    \in [Proc -> PCValues]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter  \in [SlushLoopProcess -> Nat]

=============================================================================