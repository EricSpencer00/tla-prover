---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers
    SlushQueryProcess,    \* Set of query process identifiers
    HostMapping,          \* Set of triples <<lp, qp, n>> linking processes to nodes
    SlushIterationCount,  \* Number of iterations each loop process must run
    SampleSetSize,        \* Size of the peer sample each iteration
    PickFlipThreshold,    \* Minimum number of matching replies to trigger a flip
    NoColor,              \* Special value meaning "uncolored"
    NoMessage             \* Special value meaning "no message"

\* ----------------------------------------------------------------------
\* Derived sets and convenience definitions
\* ----------------------------------------------------------------------
Colors == {"red", "blue"}

MessageTypes == {"query", "reply", "term"}

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            payload : (Colors \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,          \* [n \in Node |-> NoColor] or "red"/"blue"
    msgs,            \* Set of in‑flight messages (subset of Message)
    pc,              \* Program counters for each process
    sampleSet,       \* [lp \in SlushLoopProcess |-> {}] – peers queried this round
    iterCount        \* [lp \in SlushLoopProcess |-> 0] – iterations completed

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LpToNode(lp) ==  { n \in Node : <<lp, _, n>> \in HostMapping }
QryToNode(qp) == { n \in Node : <<_, qp, n>> \in HostMapping }
NodeToLp(n)   == { lp \in SlushLoopProcess : <<lp, _, n>> \in HostMapping }
NodeToQry(n)  == { qp \in SlushQueryProcess : <<_, qp, n>> \in HostMapping }

LoopProc(p)  == p \in SlushLoopProcess
QryProc(p)   == p \in SlushQueryProcess

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors   = [n \in Node |-> NoColor]
    /\ msgs     = {}
    /\ pc       = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Init"]
    /\ sampleSet= [lp \in SlushLoopProcess |-> {}]
    /\ iterCount= [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Client assigns a color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = "Init"
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ \E c \in Colors :
                /\ colors' = [colors EXCEPT ![n] = c]
                /\ pc'    = [pc EXCEPT !["Client"] = "Done"]
                /\ UNCHANGED <<msgs, sampleSet, iterCount>>
    \/ /\ pc["Client"] = "Done"
       /\ UNCHANGED <<colors, msgs, pc, sampleSet, iterCount>>

\* (2) Loop process waits for its node to be colored
RequireColor(lp) ==
    LET n == CHOOSE nn \in Node : <<lp, _, nn>> \in HostMapping IN
    /\ pc[lp] = "WaitColor"
    /\ colors[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* (3) Loop process selects a random sample of peers and sends queries
QuerySample(lp) ==
    LET n  == CHOOSE nn \in Node : <<lp, _, nn>> \in HostMapping IN
        peers == { qp \in SlushQueryProcess :
                     qp # (CHOOSE qpp \in SlushQueryProcess :
                                 <<_, qpp, n>> \in HostMapping) }
        sample == CHOOSE s \in SUBSET peers :
                     Cardinality(s) = SampleSetSize
    IN
    /\ pc[lp] = "Sample"
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = sample]
    /\ msgs' = msgs \cup { [type |-> "query",
                           src  |-> lp,
                           dst  |-> qp,
                           payload |-> colors[n]] :
                           qp \in sample }
    /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<colors, iterCount>>

\* (4) Query process responds to a query
RespondQry(qp) ==
    /\ pc[qp] = "Reply"
    /\ \E msg \in msgs :
          /\ msg.type = "query"
          /\ msg.dst  = qp
          /\ LET n == CHOOSE nn \in Node : <<_, qp, nn>> \in HostMapping IN
                 newColor == IF colors[n] = NoColor THEN msg.payload ELSE colors[n] IN
          /\ colors' = [colors EXCEPT ![n] = newColor]
          /\ msgs' = (msgs \ {msg}) \cup
                     { [type |-> "reply",
                        src  |-> qp,
                        dst  |-> msg.src,
                        payload |-> newColor] }
          /\ pc' = [pc EXCEPT ![qp] = "Reply"]
    \/ /\ pc[qp] = "Reply"
       /\ UNCHANGED <<colors, msgs, pc, sampleSet, iterCount>>

\* (5) Loop process tallies replies and possibly flips its node's color
ProcessReplies(lp) ==
    LET n == CHOOSE nn \in Node : <<lp, _, nn>> \in HostMapping IN
        expected == sampleSet[lp]
        received  == { m \in msgs :
                         /\ m.type = "reply"
                         /\ m.dst  = lp
                         /\ m.src \in expected }
        redCount  == Cardinality({ m \in received : m.payload = "red" })
        blueCount == Cardinality({ m \in received : m.payload = "blue" })
        newCol    == IF redCount >= PickFlipThreshold THEN "red"
                    ELSE IF blueCount >= PickFlipThreshold THEN "blue"
                    ELSE colors[n]
    IN
    /\ pc[lp] = "WaitReplies"
    /\ \A qp \in expected : \E m \in msgs :
          /\ m.type = "reply"
          /\ m.dst  = lp
          /\ m.src  = qp
    /\ colors' = [colors EXCEPT ![n] = newCol]
    /\ msgs'   = msgs \ { m \in msgs : m.type = "reply" /\ m.dst = lp }
    /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
    /\ IF iterCount[lp] + 1 < SlushIterationCount
          THEN pc' = [pc EXCEPT ![lp] = "Sample"]
          ELSE pc' = [pc EXCEPT ![lp] = "Terminate"]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ UNCHANGED <<pc, iterCount>>

\* (6) Loop process broadcasts termination
Terminate(lp) ==
    /\ pc[lp] = "Terminate"
    /\ msgs' = msgs \cup { [type |-> "term",
                            src  |-> lp,
                            dst  |-> "All",
                            payload |-> NoColor] }
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<colors, sampleSet, iterCount>>

\* (7) Query processes exit when all loop processes are done
QryExit(qp) ==
    LET allDone == \A lp \in SlushLoopProcess : pc[lp] = "Done" IN
    /\ pc[qp] = "Reply"
    /\ IF allDone
          THEN pc' = [pc EXCEPT ![qp] = "Done"]
          ELSE pc' = pc
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : QuerySample(lp)
    \/ \E qp \in SlushQueryProcess : RespondQry(qp)
    \/ \E lp \in SlushLoopProcess : ProcessReplies(lp)
    \/ \E lp \in SlushLoopProcess : Terminate(lp)
    \/ \E qp \in SlushQueryProcess : QryExit(qp)
    \/ ClientAssign

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Safety (type) invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ \A n \in Node : colors[n] \in (Colors \cup {NoColor})
    /\ \A m \in msgs :
          /\ m.type \in MessageTypes
          /\ m.src \in (SlushLoopProcess \cup SlushQueryProcess \cup {"All"})
          /\ m.dst \in (SlushLoopProcess \cup SlushQueryProcess \cup {"All"})
          /\ IF m.type = "query"   THEN m.payload \in (Colors \cup {NoColor})
             ELSE IF m.type = "reply" THEN m.payload \in Colors
                  ELSE m.payload = NoColor

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the spec minimal)
\* ----------------------------------------------------------------------
=============================================================================