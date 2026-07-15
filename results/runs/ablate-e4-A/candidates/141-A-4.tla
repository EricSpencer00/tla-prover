---- MODULE Reachable ----
EXTENDS FiniteSets, TransitiveClosure

CONSTANTS Nodes, Root, Succ, Seq

(* Derived definitions *)
SuccRel == { <<u, v>> | u \in Nodes /\ v \in Succ[u] }

ReachableSet(S) == S \cup { y : \E x \in S : <<x, y>> \in TC(SuccRel) }

VARIABLES marked, frontier, pc

(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

(* Main loop action *)
NextLoop ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ \E v \in frontier :
        /\ marked' = IF v \notin marked THEN marked \cup {v} ELSE marked
        /\ frontier' = IF v \notin marked THEN frontier \cup Succ[v] ELSE frontier \ {v}
        /\ pc' = pc

(* Termination action *)
NextTerm ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Terminated"

Next == NextLoop \/ NextTerm

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* Invariants *)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Terminated"}

Inv1 == 
    \A v \in marked : Succ[v] \subseteq marked \/ frontier

Inv2 == 
    (marked \/ ReachableSet(frontier)) = ReachableSet(marked \/ frontier)

Inv3 == 
    ReachableSet({Root}) = marked \/ ReachableSet(frontier)

PartialCorrectness == 
    ReachableSet({Root}) = marked \/ ReachableSet(frontier)

(* Liveness property *)
FiniteReachable == Finite(ReachableSet({Root}))
Termination == [] (FiniteReachable => <> (pc = "Terminated"))

====