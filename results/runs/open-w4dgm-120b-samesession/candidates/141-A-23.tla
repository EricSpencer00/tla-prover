---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

(* Misra's variant of breadth-first search: the marked (visited) set may      *)
(* overlap the frontier, which is what makes the algorithm parallel-friendly.  *)

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "terminated"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The frontier may still contain marked nodes; both cases are allowed.
Explore(f) ==
    /\ pc = "running"
    /\ f \in frontier
    /\ IF f \notin marked
         THEN /\ marked' = marked \cup {f}
              /\ frontier' = frontier \cup Succ[f]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {f}
    /\ pc' = IF frontier' = {} THEN "terminated" ELSE "running"

ExploreAny == \E f \in frontier : Explore(f)

Spec == Init /\ [][ExploreAny]_vars

(* Every successor of a marked node is accounted for: already marked or
   still waiting in the frontier. *)
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

(* Reaching a node from outside the explored part must pass through the
   frontier. *)
Inv2 == ReachFromFrontier \cup marked = ReachFromUnion

(* A node reachable from the root is either marked or reachable from the
   frontier. *)
Inv3 == ReachFromRoot = (marked \cup ReachFromFrontier)

PartialCorrectness == marked = ReachFromRoot

Termination == pc = "terminated"
====