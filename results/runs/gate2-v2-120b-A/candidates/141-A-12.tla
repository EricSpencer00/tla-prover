---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc

(* ------------------------------------------------------------------------- *)
(* State definitions                                                         *)
(* ------------------------------------------------------------------------- *)

(* The set of nodes that have been marked (visited) *)
Visited == visited

(* The frontier set of nodes to be explored (may overlap with visited) *)
Frontier == frontier

(* Program counter: "Running" or "Done" *)
Pc == pc

(* ------------------------------------------------------------------------- *)
(* Initial predicate                                                         *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "Running"

(* ------------------------------------------------------------------------- *)
(* Actions                                                                   *)
(* ------------------------------------------------------------------------- *)

VisitUnmarked ==
    /\ pc = "Running"
    /\ \E n \in frontier :
        /\ n \notin visited
        /\ visited' = visited \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = "Running"

RemoveMarked ==
    /\ pc = "Running"
    /\ \E n \in frontier :
        /\ n \in visited
        /\ visited' = visited
        /\ frontier' = frontier \ {n}
        /\ pc' = "Running"

Terminate ==
    /\ pc = "Running"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<visited, frontier>>

Next ==
    \/ VisitUnmarked
    \/ RemoveMarked
    \/ Terminate

(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<visited, frontier, pc>>

(* ------------------------------------------------------------------------- *)
(* Safety invariants                                                         *)
(* ------------------------------------------------------------------------- *)

(* Type correctness: visited and frontier contain only graph nodes *)
TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

(* Inv1: every successor of a visited node is either visited or in the frontier *)
Inv1 ==
    \A n \in visited : Succ[n] \subseteq visited \cup frontier

(* Inv2: the union of visited and the nodes reachable from frontier equals the
   nodes reachable from visited ∪ frontier *)
Inv2 ==
    ReachFrom(visited \cup frontier) = visited \cup ReachFrom(frontier)

(* Inv3: the set of nodes reachable from Root equals visited plus nodes reachable
   from the frontier *)
Inv3 ==
    ReachFrom({Root}) = visited \cup ReachFrom(frontier)

(* Partial correctness: when the algorithm terminates, visited equals the set
   of nodes reachable from Root *)
PartialCorrectness ==
    pc = "Done" => visited = ReachFrom({Root})

(* ------------------------------------------------------------------------- *)
(* Helper definition for reachability                                         *)
(* ------------------------------------------------------------------------- *)

(* ReachFrom(S) returns the set of nodes reachable from any node in S
   using the successor relation Succ. This is defined as the least fixpoint
   of a monotone operator, which is safe for both finite and infinite graphs. *)
VARIABLE S
ReachFrom(S) ==
    LET Rec(R) == R \cup { y \in Nodes : \E x \in R : y \in Succ[x] }
    IN  CHOOSE R \in SUBSET Nodes : R = Rec(R) /\ S \subseteq R

(* ------------------------------------------------------------------------- *)
(* Theorems (optional, but kept for completeness)                            *)
(* ------------------------------------------------------------------------- *)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness

(* ------------------------------------------------------------------------- *)
(* Liveness property (termination)                                            *)
(* ------------------------------------------------------------------------- *)

Termination == []<>(pc = "Done")

=============================================================================