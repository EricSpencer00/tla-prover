---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers
    SlushQueryProcess,    \* Set of query process identifiers
    HostMapping,          \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* Number of iterations each loop process must perform
    SampleSetSize,        \* Size of the peer sample taken each iteration
    PickFlipThreshold,    \* Minimum number of equal replies needed to flip
    NoColor,              \* Special value meaning “uncolored”
    NoMessage.            \* Special value meaning “no message” (unused)

\* ----------------------------------------------------------------------
\* Definitions for special constants
\* ----------------------------------------------------------------------
NoMessage == "NoMessage"

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

Process == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Message == [type   : {"query", "reply", "term"},
            src    : Process,
            dst    : Process,
            color  : Color \cup {NoColor}]

\* Helper functions to retrieve the node associated with a loop or query process
NodeOfLoop(p) == 
    CHOOSE n \in Node : <<n, p, _>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node : <<n, _, q>> \in HostMapping

QueryProcOfNode(n) == 
    CHOOSE q \in SlushQueryProcess : <<n, _, q>> \in HostMapping

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* [node -> Color \cup {NoColor}]
    msgs,    \* Set of in‑flight messages
    sample,  \* [loopProc -> SUBSET Node]  (current peer sample)
    iter,    \* [loopProc -> Nat]          (iterations completed)
    pc       \* [process -> STRING]        (program counter)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ pc = [proc \in Process |-> "Init"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* ---- Client actions ---------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "Init"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Color :
          /\ color' = [color EXCEPT ![n] = c]
          /\ UNCHANGED <<msgs, sample, iter, pc>>
          /\ pc' = [pc EXCEPT !["Client"] = "Init"]

ClientDone ==
    /\ pc["Client"] = "Init"
    /\ \A n \in Node : color[n] # NoColor
    /\ UNCHANGED <<color, msgs, sample, iter>>
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]

\* ---- Loop process actions --------------------------------------------
LoopRequireColor(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Init"
    /\ LET n == NodeOfLoop(p) IN
         /\ color[n] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "Iterate"]
         /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Iterate"
    /\ iter[p] < SlushIterationCount
    /\ LET n == NodeOfLoop(p) IN
         /\ sampleSet \in SUBSET (Node \ {n})
         /\ Cardinality(sampleSet) = SampleSetSize
         /\ sample' = [sample EXCEPT ![p] = sampleSet]
         /\ msgs' = msgs \cup
                    { [type  |-> "query",
                       src   |-> p,
                       dst   |-> QueryProcOfNode(q),
                       color |-> color[n]] : q \in sampleSet }
         /\ pc' = [pc EXCEPT ![p] = "WaitReplies"]
         /\ UNCHANGED <<color, iter>>

LoopWaitReplies(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "WaitReplies"
    /\ LET s == sample[p] IN
         /\ \A q \in s :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst  = p
                    /\ m.src  = QueryProcOfNode(q)
         /\ pc' = [pc EXCEPT ![p] = "Flip"]
         /\ UNCHANGED <<color, msgs, sample, iter>>

LoopFlip(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Flip"
    /\ LET n == NodeOfLoop(p) IN
         LET reds  == Cardinality({ m \in msgs :
                                    m.type = "reply" /\ m.dst = p /\ m.color = "Red" })
         LET blues == Cardinality({ m \in msgs :
                                    m.type = "reply" /\ m.dst = p /\ m.color = "Blue" })
         IN
            /\ IF reds >= PickFlipThreshold
               THEN color' = [color EXCEPT ![n] = "Red"]
               ELSE IF blues >= PickFlipThreshold
                    THEN color' = [color EXCEPT ![n] = "Blue"]
                    ELSE UNCHANGED color
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ iter'   = [iter EXCEPT ![p] = @ + 1]
            /\ pc' = [pc EXCEPT ![p] =
                        IF iter'[p] < SlushIterationCount
                        THEN "Iterate"
                        ELSE "Terminate"]
            /\ UNCHANGED msgs

LoopTerminate(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Terminate"
    /\ msgs' = msgs \cup
               { [type |-> "term",
                  src  |-> p,
                  dst  |-> "Client",
                  color|-> NoColor] }
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

\* ---- Query process actions -------------------------------------------
QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "Init"
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst  = q
    /\ LET n == NodeOfQuery(q) IN
         /\ LET m == CHOOSE mm \in msgs :
                     mm.type = "query" /\ mm.dst = q
                IN
            /\ IF color[n] = NoColor
               THEN color' = [color EXCEPT ![n] = m.color]
               ELSE UNCHANGED color
            /\ msgs' = msgs \cup
                       { [type  |-> "reply",
                          src   |-> q,
                          dst   |-> m.src,
                          color |-> color[n]] }
            /\ pc' = [pc EXCEPT ![q] = "Init"]
            /\ UNCHANGED <<sample, iter>>

\* ----------------------------------------------------------------------
\* Combined Next action
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in SlushLoopProcess : LoopRequireColor(p)
    \/ \E p \in SlushLoopProcess : LoopSample(p)
    \/ \E p \in SlushLoopProcess : LoopWaitReplies(p)
    \/ \E p \in SlushLoopProcess : LoopFlip(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ ClientAssign
    \/ ClientDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Color \cup {NoColor}]
    /\ msgs \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [Process -> STRING]

\* ----------------------------------------------------------------------
\* Liveness (termination) property – all processes eventually reach “Done”
\* ----------------------------------------------------------------------
Termination ==
    \A proc \in Process : <> (pc[proc] = "Done")

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====