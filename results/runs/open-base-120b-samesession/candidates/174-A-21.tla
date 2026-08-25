---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<n, lp, qp>> linking a node, its loop and query processes
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample each iteration
    PickFlipThreshold,   \* Threshold for adopting a color
    NoColor,             \* Value representing an uncolored node
    NoMessage            \* Placeholder value for “no message”

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
PROC == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Colors == {"Red", "Blue"}

Message == [type   : {"Query", "Reply", "Terminate"},
            src    : PROC,
            dst    : PROC,
            color  : NoColor \cup Colors]

\* Mapping from a loop or query process to its host node, extracted from HostMapping
LoopNode(lp) == 
    CHOOSE t \in HostMapping : t[2] = lp

QueryNode(qp) == 
    CHOOSE t \in HostMapping : t[3] = qp

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    color,      \* [Node -> (NoColor \cup Colors)]
    msgs,       \* Set of in‑flight messages
    pc,         \* [PROC -> PCState]   program counter per process
    sample,     \* [SlushLoopProcess -> SUBSET Node]   current sample set
    iter        \* [SlushLoopProcess -> Nat]   number of completed iterations

\* ----------------------------------------------------------------------
\* Types for program counters
\* ----------------------------------------------------------------------
PCState == {"Client_Ready", "Client_Done",
            "Loop_WaitColor", "Loop_Sample", "Loop_WaitReplies", "Loop_Done", "Loop_Finished",
            "Query_Loop", "Query_Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc = [p \in PROC |-> 
                IF p = "Client"          THEN "Client_Ready"
                ELSE IF p \in SlushLoopProcess THEN "Loop_WaitColor"
                ELSE "Query_Loop"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* ---- Client assigns a random color to an uncolored node ----
ClientAssign ==
    /\ pc["Client"] = "Client_Ready"
    /\ \E n \in Node : 
          /\ color[n] = NoColor
          /\ LET c \in Colors IN
                /\ color' = [color EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, pc, sample, iter>>
    /\ pc' = [pc EXCEPT !["Client"] = "Client_Ready"]

\* ---- Loop process waits until its host node is colored ----
RequireColor(lp) ==
    /\ pc[lp] = "Loop_WaitColor"
    /\ LET n == LoopNode(lp) IN
          /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Loop_Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

\* ---- Loop process selects a random sample and sends queries ----
LoopSample(lp) ==
    /\ pc[lp] = "Loop_Sample"
    /\ LET n == LoopNode(lp) IN
          /\ color[n] # NoColor
          /\ sampleSet \in SUBSET (Node \ {n})
          /\ Cardinality(sampleSet) = SampleSetSize
    /\ sample' = [sample EXCEPT ![lp] = sampleSet]
    /\ msgs' = msgs 
               \cup { [type |-> "Query",
                       src  |-> lp,
                       dst  |-> qp,
                       color|-> color[n]]
                     : qp \in SlushQueryProcess
                       /\ QueryNode(qp) \in sampleSet }
    /\ pc' = [pc EXCEPT ![lp] = "Loop_WaitReplies"]
    /\ UNCHANGED <<color, iter>>

\* ---- Query process receives a query, possibly adopts the color, and replies ----
QueryReceive(qp) ==
    /\ pc[qp] = "Query_Loop"
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst  = qp
          /\ LET n == QueryNode(qp) IN
                /\ IF color[n] = NoColor 
                      THEN color' = [color EXCEPT ![n] = m.color]
                      ELSE color' = color
                /\ reply == [type |-> "Reply",
                             src  |-> qp,
                             dst  |-> m.src,
                             color|-> color'[n]]
                /\ msgs' = (msgs \ {m}) \cup {reply}
                /\ UNCHANGED <<pc, sample, iter>>
    /\ UNCHANGED <<sample, iter>>

\* ---- Loop process collects all replies, tallies, possibly flips color, and advances ----
LoopTally(lp) ==
    /\ pc[lp] = "Loop_WaitReplies"
    /\ LET n == LoopNode(lp) IN
          /\ sampleSet == sample[lp]
          /\ replies == { m \in msgs : 
                           m.type = "Reply" /\ m.dst = lp /\ QueryNode(m.src) \in sampleSet }
          /\ Cardinality({ m.src : m \in replies }) = SampleSetSize
          /\ redCnt  == Cardinality({ m \in replies : m.color = "Red" })
          /\ blueCnt == Cardinality({ m \in replies : m.color = "Blue" })
          /\ newCol == 
                IF redCnt >= PickFlipThreshold THEN "Red"
                ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                ELSE color[n]
          /\ color' = [color EXCEPT ![n] = newCol]
          /\ msgs' = msgs \ replies
          /\ iter' = [iter EXCEPT ![lp] = @ + 1]
          /\ pc' = 
                IF iter'[lp] = SlushIterationCount 
                   THEN [pc EXCEPT ![lp] = "Loop_Done"]
                   ELSE [pc EXCEPT ![lp] = "Loop_Sample"]
          /\ sample' = [sample EXCEPT ![lp] = {}]

\* ---- Loop process broadcasts termination when finished ----
LoopTerminate(lp) ==
    /\ pc[lp] = "Loop_Done"
    /\ msgs' = msgs \cup { [type |-> "Terminate",
                            src  |-> lp,
                            dst  |-> qp,
                            color|-> NoColor]
                          : qp \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![lp] = "Loop_Finished"]
    /\ UNCHANGED <<color, sample, iter, msgs>>

\* ---- Query process consumes termination messages and eventually exits ----
QueryTerminate(qp) ==
    /\ pc[qp] = "Query_Loop"
    /\ \E m \in msgs :
          /\ m.type = "Terminate"
          /\ m.dst = qp
          /\ msgs' = msgs \ {m}
          /\ pc' = 
                IF Cardinality({ t \in msgs' : t.type = "Terminate" /\ t.dst = qp }) = 0
                   THEN [pc EXCEPT ![qp] = "Query_Done"]
                   ELSE pc
          /\ UNCHANGED <<color, sample, iter>>

\* ---- No‑op (stutter) step ----
Stutter ==
    /\ UNCHANGED <<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopSample(lp)
    \/ \E qp \in SlushQueryProcess : QueryReceive(qp)
    \/ \E lp \in SlushLoopProcess : LoopTally(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryTerminate(qp)
    \/ ClientAssign
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup Colors)]
    /\ msgs \subseteq Message
    /\ pc \in [PROC -> PCState]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Liveness property: all processes eventually finish
\* ----------------------------------------------------------------------
Termination ==
    /\ \A lp \in SlushLoopProcess : pc[lp] = "Loop_Finished"
    /\ \A qp \in SlushQueryProcess : pc[qp] = "Query_Done"
    /\ pc["Client"] = "Client_Ready"

=============================================================================