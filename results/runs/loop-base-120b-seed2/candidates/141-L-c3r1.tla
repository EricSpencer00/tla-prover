---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

(*-------------------------------------------------------------------*)
(* Helper definitions *)

(* Relation representing the graph edges *)
Rel == { p \in Nodes \X Nodes : p[2] \in Succ[p[1]] }

(* Reachability from a set of nodes (zero or more steps) *)
Reach(S) == 
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(Rel) }

(* Finite version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 3 }

(* Successor operator used by the .cfg substitution *)
ConnectedToSomeButNotAll(n) == Succ[n]

(*-------------------------------------------------------------------*)
(* State variables tuple *)

vars == <<marked, frontier, pc>>

(*-------------------------------------------------------------------*)
(* Initialization *)

Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"
    /\ TypeOK

(*-------------------------------------------------------------------*)
(* Next-state relation *)

Step == 
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier:
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "running"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "running"

Terminate == 
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate

(*-------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* Type correctness invariant *)

TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

(*-------------------------------------------------------------------*)
(* Safety invariants *)

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == (pc = "done") => (marked = Reach({Root}))

(*-------------------------------------------------------------------*)
(* Liveness property *)

Termination == <> (pc = "done")
====