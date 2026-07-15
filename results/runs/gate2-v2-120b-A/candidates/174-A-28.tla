---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be supplied in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of tuples [proc |-> p, host |-> n] linking processes to nodes
    SlushIterationCount,\* Fixed number of iterations each loop process must perform
    SampleSetSize,      \* Size of the random peer sample in each iteration
    PickFlipThreshold,  \* Minimum number of replies of a color needed to adopt it
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

MessageType == {"Query", "Reply", "Terminate"}

Message == [type : MessageType,
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            color : (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    colorAssign,    \* [node -> Colors \cup {NoColor}]
    msgs,           \* Set of in‑flight Message records
    pc,             \* [proc -> PCValue]
    sampleSet,      \* [proc -> SUBSET Node]
    iterCount       \* [proc -> Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Host(p) == 
    IF p \in SlushLoopProcess \/ p \in SlushQueryProcess
    THEN CHOOSE x \in HostMapping : x["proc"] = p
    ELSE NoMessage

NodeOf(p) == Host(p)["host"]

PCValue == {"client_assign", "loop_wait_color", "loop_query", 
           "loop_wait_replies", "loop_done", 
           "query_wait", "query_done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colorAssign = [n \in Node |-> NoColor]
    /\ msgs        = {}
    /\ pc          = [p \in (SlushLoopProcess \cup SlushQueryProcess) \cup {"Client"} |-> 
                        IF p \in SlushLoopProcess THEN "loop_wait_color"
                        ELSIF p \in SlushQueryProcess THEN "query_wait"
                        ELSE "client_assign"]
    /\ sampleSet   = [p \in SlushLoopProcess |-> {}]
    /\ iterCount   = [p \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "client_assign"
    /\ \E n \in Node :
          /\ colorAssign[n] = NoColor
          /\ LET c == CHOOSE col \in Colors : TRUE IN
                /\ colorAssign' = [colorAssign EXCEPT ![n] = c]
                /\ pc' = [pc EXCEPT !["Client"] = "client_assign"]
                /\ UNCHANGED <<msgs, sampleSet, iterCount>>
    /\ UNCHANGED <<colorAssign, pc, msgs, sampleSet, iterCount>>
    /\ IF \A n \in Node : colorAssign[n] # NoColor
        THEN pc' = [pc EXCEPT !["Client"] = "client_assign_done"]
        ELSE pc' = pc

\* 2. Loop process waits until its host node has a color
LoopWaitColor(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loop_wait_color"
    /\ colorAssign[NodeOf(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "loop_query"]
    /\ UNCHANGED <<colorAssign, msgs, sampleSet, iterCount>>

\* 3. Loop process selects a random sample and sends query messages
LoopSendQuery(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loop_query"
    /\ \E S \in SUBSET (Node \ {NodeOf(p)}) :
          /\ Cardinality(S) = SampleSetSize
          /\ LET newMsgs == { [type |-> "Query",
                               src  |-> p,
                               dst  |-> qProc,
                               color|-> colorAssign[NodeOf(p)] ] :
                             qProc \in { q \in SlushQueryProcess :
                                           NodeOf(q) \in S } } IN
                /\ msgs' = msgs \cup newMsgs
                /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
                /\ pc' = [pc EXCEPT ![p] = "loop_wait_replies"]
                /\ UNCHANGED <<colorAssign, iterCount>>
    /\ UNCHANGED <<colorAssign, iterCount, pc, msgs, sampleSet>>

\* 4. Query process handles a query message
QueryHandle(m) ==
    /\ m \in msgs
    /\ m.type = "Query"
    /\ \E qp \in SlushQueryProcess :
          /\ qp = m.dst
          /\ LET n == NodeOf(qp) IN
                /\ IF colorAssign[n] = NoColor
                   THEN /\ colorAssign' = [colorAssign EXCEPT ![n] = m.color]
                        /\ msgs'' = msgs \cup { [type |-> "Reply",
                                                 src  |-> qp,
                                                 dst  |-> m.src,
                                                 color|-> m.color] }
                   ELSE /\ colorAssign' = colorAssign
                        /\ msgs'' = msgs \cup { [type |-> "Reply",
                                                 src  |-> qp,
                                                 dst  |-> m.src,
                                                 color|-> colorAssign[n]] }
                /\ msgs' = msgs \ {m}
                /\ UNCHANGED <<sampleSet, iterCount, pc>>

\* 5. Loop process tallies replies and possibly flips its node's color
LoopTally(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loop_wait_replies"
    /\ \E replies == { m \in msgs :
                         /\ m.type = "Reply"
                         /\ m.dst = p } :
          /\ Cardinality(replies) = SampleSetSize
          /\ LET reds   == Cardinality({ m \in replies : m.color = "Red" })
                 blues  == Cardinality({ m \in replies : m.color = "Blue" })
                 curNode == NodeOf(p) IN
                /\ IF reds >= PickFlipThreshold
                      THEN colorAssign' = [colorAssign EXCEPT ![curNode] = "Red"]
                ELSE IF blues >= PickFlipThreshold
                      THEN colorAssign' = [colorAssign EXCEPT ![curNode] = "Blue"]
                ELSE colorAssign' = colorAssign
          /\ msgs' = msgs \ replies
          /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
          /\ iterCount' = [iterCount EXCEPT ![p] = @ + 1]
          /\ IF iterCount'[p] >= SlushIterationCount
                THEN pc' = [pc EXCEPT ![p] = "loop_done"]
                ELSE pc' = [pc EXCEPT ![p] = "loop_query"]
          /\ UNCHANGED <<pc, colorAssign, msgs, sampleSet, iterCount>>

\* 6. Loop process sends termination after completing all iterations
LoopTerminate(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "loop_done"
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            src  |-> p,
                            dst  |-> "All",   \* special broadcast destination
                            color|-> NoColor] }
    /\ pc' = [pc EXCEPT ![p] = "loop_done"] \* stays in done state
    /\ UNCHANGED <<colorAssign, sampleSet, iterCount>>

\* 7. Query process exits when all loop processes have terminated
QueryExit(qp) ==
    /\ qp \in SlushQueryProcess
    /\ pc[qp] = "query_wait"
    /\ \A lp \in SlushLoopProcess : pc[lp] = "loop_done"
    /\ pc' = [pc EXCEPT ![qp] = "query_done"]
    /\ UNCHANGED <<colorAssign, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Composite next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in SlushLoopProcess : LoopWaitColor(p)
    \/ \E p \in SlushLoopProcess : LoopSendQuery(p)
    \/ \E m \in msgs : QueryHandle(m)
    \/ \E p \in SlushLoopProcess : LoopTally(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colorAssign, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (the only required invariant)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : colorAssign[n] \in Colors \cup {NoColor}
    /\ \A m \in msgs :
          /\ m.type \in MessageType
          /\ m.src  \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"})
          /\ m.dst   \in (SlushLoopProcess \cup SlushQueryProcess \cup {"All", "Client"})
          /\ m.color \in Colors \cup {NoColor}
    /\ \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) : pc[p] \in PCValue
    /\ \A p \in SlushLoopProcess : sampleSet[p] \subseteq Node \ {NodeOf(p)} /\ Cardinality(sampleSet[p]) <= SampleSetSize
    /\ \A p \in SlushLoopProcess : iterCount[p] \in Nat

\* ----------------------------------------------------------------------
\* Termination property (optional, not the invariant)
\* ----------------------------------------------------------------------
Termination == 
    \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) :
        pc[p] \in {"loop_done", "query_done", "client_assign_done"}

====