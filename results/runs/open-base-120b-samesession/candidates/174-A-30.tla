---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                \* Set of all node identifiers
    SlushLoopProcess,    \* Set of loop processes (one per node)
    SlushQueryProcess,   \* Set of query processes (one per node)
    HostMapping,         \* Set of triples <<node, loop, query>>
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample taken each round
    PickFlipThreshold,   \* Minimum number of replies of one color to trigger a flip
    NoColor,             \* Sentinel value meaning “uncolored”
    NoMessage            \* Sentinel value used in termination messages

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Message == [type   : {"query", "reply", "term"},
            src    : Proc,
            dst    : Proc,
            color  : (NoColor \cup {"Red", "Blue"} \cup NoMessage)]

NodeOfLoop(l) == 
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,   \* [Node -> (NoColor \cup {"Red","Blue"})]
    msgs,     \* SUBSET Message
    pc,       \* [Proc -> Nat]   (program counter for each process)
    sample,   \* [SlushLoopProcess -> SUBSET Node]  (current peer sample)
    iter      \* [SlushLoopProcess -> Nat]          (iterations completed)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in Proc |-> 0]          \* 0 = start state for every process
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = 0
    /\ \E n \in Node : colors[n] = NoColor
    /\ col \in {"Red","Blue"}
    /\ colors' = [colors EXCEPT ![n] = col]
    /\ pc'     = [pc EXCEPT !["Client"] = 0]   \* keep client alive until all colored
    /\ UNCHANGED << msgs, sample, iter >>

ClientDone ==
    /\ pc["Client"] = 0
    /\ \A n \in Node : colors[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = 1]       \* 1 = done
    /\ UNCHANGED << colors, msgs, sample, iter >>

LoopRequireColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 0
    /\ colors[NodeOfLoop(l)] # NoColor
    /\ pc' = [pc EXCEPT ![l] = 1]              \* 1 = ready to sample
    /\ UNCHANGED << colors, msgs, sample, iter >>

LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 1
    /\ let n == NodeOfLoop(l) in
       sampleSet == CHOOSE s \subseteq Node \ {n} :
                     Cardinality(s) = SampleSetSize
    in
    /\ sample' = [sample EXCEPT ![l] = sampleSet]
    /\ let qs == { q \in SlushQueryProcess : NodeOfQuery(q) \in sampleSet } in
       msgs' = msgs \cup
               { [type |-> "query",
                  src  |-> l,
                  dst  |-> q,
                  color|-> colors[n]] : q \in qs }
    /\ pc' = [pc EXCEPT ![l] = 2]              \* 2 = waiting for replies
    /\ UNCHANGED << colors, iter >>

QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs : m.type = "query" /\ m.dst = q
    /\ let m == CHOOSE mm \in msgs : mm.type = "query" /\ mm.dst = q in
       n == NodeOfQuery(q)
    /\ IF colors[n] = NoColor
          THEN colors' = [colors EXCEPT ![n] = m.color]
          ELSE colors' = colors
    /\ msgs' = (msgs \ {m}) \cup
               { [type |-> "reply",
                  src  |-> q,
                  dst  |-> m.src,
                  color|-> colors'[n]] }
    /\ UNCHANGED << pc, sample, iter >>

LoopTally(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 2
    /\ let n  == NodeOfLoop(l)
           s  == sample[l]
           qs == { q \in SlushQueryProcess : NodeOfQuery(q) \in s }
           replies == { m \in msgs :
                         m.type = "reply" /\ m.dst = l /\ m.src \in qs }
       in
    /\ Cardinality(replies) = SampleSetSize
    /\ reds  == Cardinality({ m \in replies : m.color = "Red" })
    /\ blues == Cardinality({ m \in replies : m.color = "Blue" })
    /\ newColor ==
          IF reds  >= PickFlipThreshold THEN "Red"
          ELSE IF blues >= PickFlipThreshold THEN "Blue"
          ELSE colors[n]
    /\ colors' = [colors EXCEPT ![n] = newColor]
    /\ msgsTmp = msgs \ replies
    /\ iter'   = [iter EXCEPT ![l] = @ + 1]
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ IF iter'[l] = SlushIterationCount
          THEN /\ pc' = [pc EXCEPT ![l] = 3]        \* 3 = terminated
               /\ msgs' = msgsTmp \cup
                         { [type |-> "term",
                            src  |-> l,
                            dst  |-> q,
                            color|-> NoMessage] : q \in SlushQueryProcess }
          ELSE /\ pc' = [pc EXCEPT ![l] = 1]        \* back to next round
               /\ msgs' = msgsTmp
    /\ UNCHANGED << >>

LoopTerminate(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = 3
    /\ UNCHANGED << colors, msgs, pc, sample, iter >>

QueryTerminate(q) ==
    /\ q \in SlushQueryProcess
    /\ \A l \in SlushLoopProcess : pc[l] = 3
    /\ pc' = [pc EXCEPT ![q] = 4]                \* 4 = done
    /\ UNCHANGED << colors, msgs, sample, iter >>

Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ \E l \in SlushLoopProcess : LoopRequireColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryTerminate(q)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (NoColor \cup {"Red","Blue"})]
    /\ msgs   \subseteq Message
    /\ pc \in [Proc -> Nat]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]

=============================================================================