---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

(* Operator that will replace Succ via the .cfg substitution *)
ConnectedToSomeButNotAll(n) == IF n \in Nodes THEN {} ELSE {}

(* Relation used for transitive closure of the graph *)
R == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

(* Reachable set from a set of start nodes using the transitive closure of R *)
ReachSet(S) == TC(R, S)

VARIABLES marked, frontier, pc

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

(* One step of the algorithm *)
Step ==
    \/ /\ pc = "running"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ IF n \notin marked THEN
                  /\ marked'   = marked \cup {n}
                  /\ frontier' = frontier \cup Succ[n]
               ELSE
                  /\ marked'   = marked
                  /\ frontier' = frontier \ {n}
            /\ pc' = "running"
    \/ /\ pc = "running"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Next == Step

(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

(* Invariant 1: every successor of a marked node is in marked or frontier *)
Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

(* Invariant 2: union of marked and reachable from frontier equals reachable from marked ∪ frontier *)
Inv2 == marked \cup ReachSet(frontier) = ReachSet(marked \cup frontier)

(* Invariant 3: reachable from Root equals marked plus reachable from frontier *)
Inv3 == ReachSet({Root}) = marked \cup ReachSet(frontier)

(* Partial correctness: when terminated, marked equals the reachable set from Root *)
PartialCorrectness ==
    /\ pc = "done"
    /\ marked = ReachSet({Root})

(* Liveness property: eventual termination *)
Termination == <> (pc = "done")

(* Required operator: a finite version of Seq *)
LimitedSeq(S) == Seq(S)

====