---- MODULE ReachableProofs ----
EXTENDS SequentialReachability, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Invariant 1 : type correctness and successor condition
   ---------------------------------------------------------------------- *)
Invariant1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* ----------------------------------------------------------------------
   Invariant 2 : relationship between marked set, frontier and reachability
   ---------------------------------------------------------------------- *)
Invariant2 ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(* ----------------------------------------------------------------------
   Invariant 3 : reachability from the root
   ---------------------------------------------------------------------- *)
Invariant3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

(* ----------------------------------------------------------------------
   Collection of invariants for TLC
   ---------------------------------------------------------------------- *)
INVARIANTS == {Invariant1, Invariant2, Invariant3}

(* ----------------------------------------------------------------------
   Initial state (exact initialization is not specified in the description)
   ---------------------------------------------------------------------- *)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Init"

(* ----------------------------------------------------------------------
   Abstract step relation (the concrete algorithm is defined elsewhere)
   ---------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "Init"
     /\ pc' = "Run"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Run"
     /\ (* abstract algorithm step – may modify marked/frontier *)
        marked' \in SUBSET Nodes
        frontier' \in SUBSET Nodes
        pc' = "Run"
  \/ /\ pc = "Run"
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>

Termination == pc = "Done"

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Desired property: partial correctness upon termination
   ---------------------------------------------------------------------- *)
Properties ==
  Termination => marked = Reachable({Root})

====