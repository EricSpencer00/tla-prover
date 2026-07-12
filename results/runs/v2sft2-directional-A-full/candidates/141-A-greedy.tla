---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Type correctness invariant: both sets contain only nodes from Nodes
   ---------------------------------------------------------------------- *)
TypeOK == 
    marked \subseteq Nodes /\ 
    frontier \subseteq Nodes

(* ----------------------------------------------------------------------
   Initial state: marked empty, frontier contains only Root, pc = "Start"
   ---------------------------------------------------------------------- *)
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Start"

(* ----------------------------------------------------------------------
   Main action: nondeterministically pick a node from the frontier
   ---------------------------------------------------------------------- *)
Main ==
    /\ pc = "Start"
    /\ \E v \in frontier :
        \/ /\ v \notin marked
           /\ marked' = marked \cup {v}
           /\ frontier' = frontier \cup Succ[v]
           /\ pc' = "Start"
        \/ /\ v \in marked
           /\ frontier' = frontier \ {v}
           /\ pc' = "Start"
    /\ UNCHANGED marked

(* ----------------------------------------------------------------------
   Termination condition: when frontier is empty, the algorithm stops
   ---------------------------------------------------------------------- *)
Terminate ==
    /\ pc = "Start"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

(* ----------------------------------------------------------------------
   Next-state relation: either Main or Terminate
   ---------------------------------------------------------------------- *)
Next == Main \/ Terminate

(* ----------------------------------------------------------------------
   Specification: the system starts in Init and evolves according to Next
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Safety invariants
   ---------------------------------------------------------------------- *)

(* Inv1: every successor of a marked node is either marked or in the frontier *)
Inv1 == 
    \A v \in marked : 
        Succ[v] \subseteq marked \cup frontier

(* Inv2: the union of marked and nodes reachable from frontier equals
        the nodes reachable from the union of marked and frontier *)
Inv2 ==
    (marked \cup ReachableFrom(frontier)) =
    ReachableFrom(marked \cup frontier)

(* Inv3: the nodes reachable from Root equal the marked set plus nodes
        reachable from the frontier *)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

(* Partial correctness invariant: when the algorithm terminates,
   the marked set equals the set of nodes reachable from Root *)
PartialCorrectness ==
    (pc = "Done") => (marked = ReachableFrom({Root}))

(* ----------------------------------------------------------------------
   Helper function: transitive closure of Succ over a set of nodes
   ---------------------------------------------------------------------- *)
ReachableFrom(S) ==
    LET
        step(x) == Succ[x]
    IN
        { y \in Nodes : y \in S \/ ( \E x \in S : y \in step(x) ) }

(* ----------------------------------------------------------------------
   Liveness property: termination when the reachable set is finite
   ---------------------------------------------------------------------- *)
Termination == 
    WF_vars(Next)

====