---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityLemmas, FiniteSets, Naturals, TLC

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*--------------------------------------------------------------------
  Definitions imported from the sequential reachability algorithm module
--------------------------------------------------------------------*)
INIT == SeqReachability.INIT
NEXT == SeqReachability.NEXT

(*--------------------------------------------------------------------
  The set of all state variables (used for stuttering)
--------------------------------------------------------------------*)
vars == <<Marked, Frontier, pc>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == INIT /\ [][NEXT]_vars

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Succ(n) == { m \in Nodes : <<n, m>> \in Edges }

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
Invariant1 ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ \A n \in Marked : Succ(n) \subseteq Marked \cup Frontier

Invariant2 ==
  Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

Invariant3 ==
  Reachable({Root}) = Marked \cup Reachable(Frontier)

INVARIANTS == {Invariant1, Invariant2, Invariant3}

(*--------------------------------------------------------------------
  Properties (here we expose the same invariants as safety properties)
--------------------------------------------------------------------*)
PROPERTIES == INVARIANTS

====