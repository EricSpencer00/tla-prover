---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Initial condition
-----------------------------------------------------------------*)
INIT ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "start"
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes

(*-----------------------------------------------------------------
  Next-state relation (a simple abstraction of the algorithm)
-----------------------------------------------------------------*)
NEXT ==
  \/ /\ pc = "start"
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>
  \/ /\ pc = "start"
     /\ UNCHANGED <<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked :
        \A m \in Succ[n] :
          m \in Marked \/ m \in Frontier

Inv2 ==
  (Marked \cup ReachableFrom(Frontier)) = ReachableFrom(Marked \cup Frontier)

Inv3 ==
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

INVARIANTS == { Inv1, Inv2, Inv3 }

(*-----------------------------------------------------------------
  Partial‑correctness property
-----------------------------------------------------------------*)
TerminationCorrectness ==
  /\ pc = "done"
  => Marked = ReachableFrom({Root})

PROPERTIES == { TerminationCorrectness }

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec ==
  INIT /\ [][NEXT]_<<Marked, Frontier, pc>>

====