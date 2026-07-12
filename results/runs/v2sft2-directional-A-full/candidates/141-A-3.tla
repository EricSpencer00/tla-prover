---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES Marked, Frontier, PC

(* Type correctness invariant: both sets contain only graph nodes *)
TypeOK == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes

(* Initial state: empty marked set, frontier contains only the root, main loop *)
Init == 
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ PC = "Loop"

(* Main action: nondeterministically pick a node from the frontier *)
Main ==
    \E n \in Frontier :
        IF n \in Marked THEN
            /\ Frontier' = Frontier \ {n}
            /\ PC' = "Loop"
        ELSE
            /\ Marked' = Marked \cup {n}
            /\ Frontier' = Frontier \cup (Succ[n])
            /\ PC' = "Loop"

(* Next-state relation *)
Next == Main

(* Complete specification *)
Spec == Init /\ [][Next]_<<Marked, Frontier, PC>>

(* Safety invariants *)

(* 1. Every successor of a marked node is either marked or in the frontier *)
Inv1 == 
    \A n \in Marked :
        (Succ[n] \subseteq Marked) \/ (Succ[n] \subseteq Frontier)

(* 2. The union of the marked set and the nodes reachable from the frontier 
    equals the nodes reachable from the union of marked and frontier *)
Inv2 ==
    LET ReachableSet(S) == {x \in Nodes : \E y \in S : y = x \/ x \in Succ[y]}
    IN  ReachableSet(Marked \cup Frontier) = 
        ReachableSet(Marked) \cup ReachableSet(Frontier)

(* 3. The set of nodes reachable from the root equals the marked set 
    plus nodes reachable from the frontier *)
Inv3 ==
    LET ReachableRoot == {x \in Nodes : \E y \in Succ* [Root] : y = x}
        ReachFromFrontier == {x \in Nodes : \E y \in Frontier : y = x \/ x \in Succ[y]}
    IN  ReachableRoot = Marked \cup ReachFromFrontier

(* Partial correctness invariant: when the algorithm terminates, 
    the marked set equals the set of nodes reachable from the root *)
PartialCorrectness ==
    (PC = "Done") => (Marked = {x \in Nodes : \E y \in Succ* [Root] : y = x})

(* Termination property (classical liveness, not used by TLC but included) *)
Termination ==
    [] (PC = "Done")

====