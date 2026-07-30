---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

(* Misra's variant of breadth-first search: the visited (marked) set and the     *)
(* frontier set may overlap, which is what makes it suitable for parallel        *)
(* implementation. The .cfg substitutes ConnectedToSomeButNotAll for Succ below,  *)
(* so Succ is left as a declared constant here.                                   *)

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE
        LET x == CHOOSE y \in S : TRUE
            tx == {z \in Nodes : z \in Succ[x]}
        IN x \cup ReachFrom(S \ {x}) \cup ReachFrom(tx)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Step ==
    \E x \in frontier :
        /\ frontier' = frontier \ {x}
        /\ \/ /\ x \notin marked
              /\ marked' = marked \cup {x}
              /\ frontier' = frontier' \cup Succ[x]
           \/ /\ x \in marked
              /\ marked' = marked
        /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == Step

(* Misra's key invariant: successors of marked nodes always lie in marked or *)
(* frontier, so none are lost between the two overlapping sets.              *)
Inv1 ==
    \A x \in marked : Succ[x] \subseteq marked \cup frontier

(* Frontier plus marked covers the same reachable nodes as the union of both. *)
Inv2 ==
    ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)

(* No reachable node is hidden far away: the reachable set is exactly marked   *)
(* plus whatever is reachable from the frontier.                               *)
Inv3 ==
    ReachFrom(Nodes) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = ReachFrom(Nodes)

Spec == Init /\ [][Step]_vars

Termination == (pc # "done") ~> (pc = "done")

(* The .cfg substitutes ConnectedToSomeButNotAll for Succ, so Succ is left     *)
(* declared as a constant. The .cfg also substitutes LimitedSeq for Seq, so    *)
(* we do not redeclare it here and keep EXTENDS Sequences.                     *)
====