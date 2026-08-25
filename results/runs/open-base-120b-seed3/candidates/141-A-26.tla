---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(* Edge relation derived from the successor function *)
Edge == [n \in Nodes |-> Succ[n]]

(* Reachability from a set of nodes using transitive closure *)
Reach(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) }

(* Operator required by the .cfg substitution *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* LimitedSeq replaces Seq from the Sequences module *)
LimitedSeq(S) == Seq(S)

(* ---------------------------------------------------------------------- *)
(* Initialization *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ TypeOK

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
    \/ /\ frontier # {}
       /\ \E n \in frontier :
            /\ n \notin marked
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc'       = pc
    \/ /\ frontier # {}
       /\ \E n \in frontier :
            /\ n \in marked
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ pc'       = pc
    \/ /\ frontier = {}
       /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
       => marked = Reach({Root})

(* ---------------------------------------------------------------------- *)
(* Liveness property *)

Termination == <> (frontier = {})

====