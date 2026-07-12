---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Nodes, Root, Succ, Seq

(* ----------------------------------------------------------------------
   Derived types
   ---------------------------------------------------------------------- *)
Node == Nodes
SuccSet(n) == IF n \in Nodes THEN Succ[n] ELSE {}

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Reachable(n) == n = Root \/ \/ n \in Succ[*Root]  (* simple reflexive transitive closure *)

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Initial state (inherited and instantiated)
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "mark"

(* ----------------------------------------------------------------------
   Actions (inherited behavior)
   ---------------------------------------------------------------------- *)
Mark ==
    /\ pc = "mark"
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "add"

Add ==
    /\ pc = "add"
    /\ frontier' = \E n \in frontier : Succ[n]
    /\ pc' = "add"

(* The algorithm completes when no new nodes can be added *)
Complete ==
    /\ pc = "add"
    /\ frontier = {}

Next ==
    \/ Mark
    \/ Add

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"mark", "add"}

(* ----------------------------------------------------------------------
   Algorithm invariants
   ---------------------------------------------------------------------- *)
Inv1 == marked \subseteq Reachable(Root)

Inv2 == frontier \subseteq Reachable(Root)

Inv3 == marked \cup frontier \subseteq Reachable(Root)

PartialCorrectness == 
    /\ marked \cup frontier \subseteq Reachable(Root)
    /\ Reachable(Root) \subseteq marked \cup frontier

(* ----------------------------------------------------------------------
   Liveness property
   ---------------------------------------------------------------------- *)
Termination == <> Complete

====