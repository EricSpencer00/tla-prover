---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, 
        SeqReachability,      \* the sequential reachability algorithm module
        ReachabilityLemmas    \* the module containing the graph‑theoretic lemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State variable tuple (used by the temporal operator)
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial predicate (taken from the algorithm module)
\* ----------------------------------------------------------------------
INIT == Init

\* ----------------------------------------------------------------------
\* Next‑state relation (taken from the algorithm module)
\* ----------------------------------------------------------------------
NEXT == Next

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
TypeCorrect ==
   /\ marked \subseteq Nodes
   /\ frontier \subseteq Nodes
   /\ pc \in {"init", "step", "done"}

SuccessorInv ==
   \A n \in marked :
      \A s \in Succ[n] : s \in marked \cup frontier

Invariant1 == TypeCorrect /\ SuccessorInv

\* ----------------------------------------------------------------------
\* Invariant 2:   marked ∪ ReachableFrom(frontier) = ReachableFrom(marked ∪ frontier)
\* (proved from Lemma 1 in ReachabilityLemmas)
\* ----------------------------------------------------------------------
Invariant2 == 
   marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3:   ReachableFrom({Root}) = marked ∪ ReachableFrom(frontier)
\* (proved from Lemma 2 and Lemma 3 in ReachabilityLemmas)
\* ----------------------------------------------------------------------
Invariant3 == 
   ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* Collection of all inductive invariants required by TLC
\* ----------------------------------------------------------------------
INVARIANTS == /\ Invariant1 /\ Invariant2 /\ Invariant3

\* ----------------------------------------------------------------------
\* Partial‑correctness property (theorem statement for TLAPS)
\* ----------------------------------------------------------------------
PartialCorrectness ==
   \A s \in [][NEXT]_vars :
      (pc = "done" => marked = ReachableFrom({Root}))

\* ----------------------------------------------------------------------
\* Set of properties supplied to the model checker
\* ----------------------------------------------------------------------
PROPERTIES == /\ Invariant1 /\ Invariant2 /\ Invariant3 /\ PartialCorrectness

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == INIT /\ [][NEXT]_vars

====