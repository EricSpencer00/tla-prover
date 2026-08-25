---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*-----------------------------------------------------------------
  Initial predicate and next-state relation are taken from the
  sequential reachability algorithm module.
-----------------------------------------------------------------*)
Init == SeqReachAlg.Init
Next == SeqReachAlg.Next

(*-----------------------------------------------------------------
  Invariant 1: type correctness and successor property
-----------------------------------------------------------------*)
Inv1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"init", "step", "done"}
  /\ \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

(*-----------------------------------------------------------------
  Invariant 2: marked ∪ Reachable(Frontier) = Reachable(Marked ∪ Frontier)
-----------------------------------------------------------------*)
Inv2 ==
  Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

(*-----------------------------------------------------------------
  Invariant 3: Reachable({Root}) = marked ∪ Reachable(Frontier)
-----------------------------------------------------------------*)
Inv3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

(*-----------------------------------------------------------------
  Partial‑correctness property: when the algorithm terminates,
  the set of marked nodes equals the reachable set from the root.
-----------------------------------------------------------------*)
Correctness ==
  (pc = "done") => (Marked = Reachable({Root}))

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*-----------------------------------------------------------------
  Collections required by the configuration file
-----------------------------------------------------------------*)
INVARIANTS == {Inv1, Inv2, Inv3}
PROPERTIES == {Correctness}
====