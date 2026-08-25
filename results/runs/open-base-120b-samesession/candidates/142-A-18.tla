---- MODULE ReachableProofs ----
EXTENDS Naturals, SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

(* The sequential algorithm module is assumed to provide Init and Next actions.
   The reachability‑lemmas module is assumed to provide:
     - Succ : [Nodes -> SUBSET Nodes]   (the successor function)
     - Reachable(S) : SUBSET Nodes      (nodes reachable from a set S) *)

INIT == Init

NEXT == Next

Inv1 == /\ marked \subseteq Nodes
        /\ frontier \subseteq Nodes
        /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Inv3 == Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

Spec == INIT /\ [][NEXT]_vars

PROPERTIES == {Spec}
====