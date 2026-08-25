---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

\* State variables inherited from the sequential algorithm
VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

\* Assumptions about the graph structure (provided by the extended modules)
ASSUME Succ \in [Nodes -> SUBSET Nodes]
ASSUME ReachFrom \in [SUBSET Nodes -> SUBSET Nodes]

\* Initial state
Init == /\ Marked = {}
        /\ Frontier = {Root}
        /\ pc = "run"

\* Transition relation (as defined by the sequential algorithm)
Next ==
  \/ /\ pc = "run"
     /\ \E n \in Frontier:
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked')
          /\ pc' = IF Frontier' = {} THEN "done" ELSE "run"
  \/ /\ pc = "done"
     /\ UNCHANGED <<Marked, Frontier, pc>>

\* Invariant 1: type correctness and successor condition
Inv1 == /\ Marked \subseteq Nodes
        /\ Frontier \subseteq Nodes
        /\ pc \in {"run", "done"}
        /\ \A m \in Marked: Succ[m] \subseteq Marked \cup Frontier

\* Invariant 2: reachability equivalence using Lemma 1
Inv2 == (Marked \cup ReachFrom(Frontier)) = ReachFrom(Marked \cup Frontier)

\* Invariant 3: reachability from the root using Lemma 2 and Lemma 3
Inv3 == ReachFrom({Root}) = Marked \cup ReachFrom(Frontier)

\* Final theorem: partial correctness upon termination
FinalTheorem == /\ pc = "done"
                /\ Marked = ReachFrom({Root})

\* Specification
Spec == Init /\ [][Next]_vars

\* Collection of invariants for the TLC configuration
INVARIANTS == <<Inv1, Inv2, Inv3>>

\* Properties to be checked (the partial‑correctness theorem)
PROPERTIES == <<FinalTheorem>>

====