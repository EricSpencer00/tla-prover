---- MODULE ReachableProofs ----
EXTENDS FiniteSets, Naturals, Sequences, 
        SeqReachAlg,        \* the sequential reachability algorithm
        ReachabilityLemmas  \* graph‑theoretic lemmas used in the proofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\*  State initialization – delegated to the algorithm module
\* ----------------------------------------------------------------------
Init == SeqReachAlg!Init

\* ----------------------------------------------------------------------
\*  State transition – delegated to the algorithm module
\* ----------------------------------------------------------------------
Next == SeqReachAlg!Next

\* ----------------------------------------------------------------------
\*  Invariant 1 : type correctness and successor closure
\* ----------------------------------------------------------------------
Inv1 == /\ marked \subseteq Nodes
        /\ frontier \subseteq Nodes
        /\ \A n \in marked :
              \A s \in Succ[n] : s \in marked \/ frontier

\* ----------------------------------------------------------------------
\*  Invariant 2 : reachable‑from‑frontier characterisation (Lemma 1)
\* ----------------------------------------------------------------------
Inv2 == (marked \cup ReachFrom(frontier)) = 
        ReachFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\*  Invariant 3 : marked set equals reachable set up to frontier
\*               (Lemma 2 and Lemma 3)
\* ----------------------------------------------------------------------
Inv3 == ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* ----------------------------------------------------------------------
\*  Collection of all invariants required by the specification
\* ----------------------------------------------------------------------
INVARIANTS == <<Inv1, Inv2, Inv3>>

\* ----------------------------------------------------------------------
\*  Partial‑correctness theorem (the final property)
\* ----------------------------------------------------------------------
Theorem == 
  /\ Spec
  /\ []Inv1
  /\ []Inv2
  /\ []Inv3
  =>  [] (Terminated => marked = ReachFrom({Root}))

\* ----------------------------------------------------------------------
\*  Set of properties that TLC should check
\* ----------------------------------------------------------------------
PROPERTIES == <<Theorem>>

\* ----------------------------------------------------------------------
\*  The complete specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

====