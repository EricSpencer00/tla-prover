---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* ----------------------------------------------------------------------
   CONSTANTS
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root, Succ, Seq

(* ----------------------------------------------------------------------
   VARIABLES
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   TYPEOK invariant: both marked and frontier contain only elements of Nodes
   ---------------------------------------------------------------------- *)
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

(* ----------------------------------------------------------------------
   Initial state:
     - marked is empty
     - frontier contains only the root node
     - program counter is "Start"
   ---------------------------------------------------------------------- *)
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Start"

(* ----------------------------------------------------------------------
   Helper: Determine the set of nodes reachable from the current frontier
   ---------------------------------------------------------------------- *)
ReachFromFrontier == 
    \E seq \in Seq :  /\ seq = {}
                      \/ /\ seq \in Seq
                         /\ Head(seq) \in frontier
                         /\ ReachFromFrontier( Tail(seq) )

(* ----------------------------------------------------------------------
   Main action (one step of the algorithm)
   ---------------------------------------------------------------------- *)
Main ==
    /\ pc = "Start"
    /\ /\ frontier # {}
       /\ \E v \in frontier :
            (   /\ ~(v \in marked)
                /\ marked' = marked \cup {v}
                /\ frontier' = frontier \cup Succ[v]
            \/ /\ (v \in marked)
                /\ frontier' = frontier \ {v}
            )
       /\ pc' = "Start"
    /\ UNCHANGED <<marked, pc>>

(* ----------------------------------------------------------------------
   NEXT action (no other actions)
   ---------------------------------------------------------------------- *)
Next == Main

(* ----------------------------------------------------------------------
   Specification: the system starts in Init and repeatedly takes steps defined by Next
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariant Inv1: every successor of a marked node is in marked or frontier
   ---------------------------------------------------------------------- *)
Inv1 == \A n \in marked : (Succ[n] \subseteq (marked \cup frontier))

(* ----------------------------------------------------------------------
   Invariant Inv2: the union of marked and nodes reachable from the frontier
   equals the nodes reachable from the union of marked and frontier
   ---------------------------------------------------------------------- *)
Inv2 == 
    (marked \cup ReachFromFrontier) = 
    (Succ[marked \cup frontier])

(* ----------------------------------------------------------------------
   Invariant Inv3: nodes reachable from root equal marked plus reachable from frontier
   ---------------------------------------------------------------------- *)
Inv3 == 
    Succ[{Root}] = marked \cup ReachFromFrontier

(* ----------------------------------------------------------------------
   PartialCorrectness invariant: when frontier is empty, marked equals reachable set
   ---------------------------------------------------------------------- *)
PartialCorrectness == 
    frontier = {} => marked = Succ[{Root}]

(* ----------------------------------------------------------------------
   TERMINATION property (weak fairness of the main action)
   ---------------------------------------------------------------------- *)
Termination == WF_vars(Main, <<marked, frontier, pc>>)

====