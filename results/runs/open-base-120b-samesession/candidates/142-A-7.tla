---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences
EXTENDS SeqReachabilityAlg      \* the sequential reachability algorithm
EXTENDS ReachabilityLemmas      \* graph‑theoretic lemmas used in the proofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions (taken from the extended modules)
\* ----------------------------------------------------------------------
vars == <<Marked, Frontier, pc>>

\* The algorithm's initial state and transition relation are imported.
\* We give them the required names for the specification.
Init == InitAlg
Next == NextAlg

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
\* ----------------------------------------------------------------------
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in Succ[n] :
          s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ reachable(Frontier) = reachable(marked ∪ Frontier)
\* ----------------------------------------------------------------------
Inv2 ==
  Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: reachable from the root equals marked ∪ reachable(Frontier)
\* ----------------------------------------------------------------------
Inv3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

\* ----------------------------------------------------------------------
\* Collection of invariants required by the model checker
\* ----------------------------------------------------------------------
INVARIANTS == <<Inv1, Inv2, Inv3>>

\* ----------------------------------------------------------------------
\* Termination condition (program counter indicates the algorithm is done)
\* ----------------------------------------------------------------------
Termination == pc = "Done"

\* ----------------------------------------------------------------------
\* Partial‑correctness property: when the algorithm terminates,
\* the set of marked nodes equals the set of nodes reachable from the root.
\* ----------------------------------------------------------------------
PartialCorrectness == Termination => Marked = Reachable({Root})

PROPERTIES == <<PartialCorrectness>>

\* ----------------------------------------------------------------------
\* The complete specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

====