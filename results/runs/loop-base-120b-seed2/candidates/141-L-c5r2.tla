---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* A finite version of Seq for model checking *)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= 10 }

(* Limited successor operator – replaces Succ in the cfg *)
ConnectedToSomeButNotAll(n) == Succ[n] \cap Nodes

(* Relation used for reachability *)
R == { <<x, y>> : x \in Nodes /\ y \in ConnectedToSomeButNotAll(x) }

(* Nodes reachable from a set S via the successor relation *)
Reach(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(R) }

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(* Main step – nondeterministically choose a node from the frontier *)
Next ==
    \/ \E n \in frontier :
        /\ n \notin marked
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
        /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"
    \/ \E n \in frontier :
        /\ n \in marked
        /\ marked'   = marked
        /\ frontier' = frontier \ {n}
        /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"

(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Type correctness invariant *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

(* Invariant 1: successors of marked nodes stay in marked ∪ frontier *)
Inv1 == \A m \in marked : ConnectedToSomeButNotAll(m) \subseteq marked \cup frontier

(* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier) *)
Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

(* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier) *)
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

(* Partial correctness: when the algorithm terminates, marked = reachable from Root *)
PartialCorrectness == (frontier = {}) => (marked = Reach({Root}))

(* Liveness property: the algorithm eventually terminates *)
Termination == <> (frontier = {})

====