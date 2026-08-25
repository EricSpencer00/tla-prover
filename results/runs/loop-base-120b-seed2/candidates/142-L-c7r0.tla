---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences,
        SequentialReachability,   \* the algorithm's definition
        ReachabilityLemmas        \* graph‑theoretic lemmas used in the proofs

CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* State variables (as defined in SequentialReachability)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Initial predicate (delegated to the algorithm module)
\* ----------------------------------------------------------------------
Init == SequentialReachability.Init

\* ----------------------------------------------------------------------
\* Next‑state relation (delegated to the algorithm module)
\* ----------------------------------------------------------------------
Next == SequentialReachability.Next

\* ----------------------------------------------------------------------
\* Reachability operator (provided by ReachabilityLemmas)
\* ----------------------------------------------------------------------
Reachable(S) == ReachabilityLemmas.Reachable(S)

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and closure under successors
\* ----------------------------------------------------------------------
Invariant1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A s \in ReachabilityLemmas.Successors(n) :
          s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: Lemma 1 (direct consequence)
\* ----------------------------------------------------------------------
Invariant2 ==
  Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Lemmas 2 and 3
\* ----------------------------------------------------------------------
Invariant3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

\* ----------------------------------------------------------------------
\* Collection of all invariants required by TLC
\* ----------------------------------------------------------------------
INVARIANTS ==
  /\ Invariant1
  /\ Invariant2
  /\ Invariant3

\* ----------------------------------------------------------------------
\* Termination predicate (the algorithm’s final control state)
\* ----------------------------------------------------------------------
Terminated == pc = "done"

\* ----------------------------------------------------------------------
\* Partial‑correctness theorem (the final property)
\* ----------------------------------------------------------------------
PartialCorrectness ==
  Terminated => Marked = Reachable({Root})

\* ----------------------------------------------------------------------
\* Collection of properties to be checked by TLC
\* ----------------------------------------------------------------------
PROPERTIES == PartialCorrectness

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg file
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_(<<Marked, Frontier, pc>>)

====