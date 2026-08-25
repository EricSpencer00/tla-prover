---- MODULE ReachableProofs ----
EXTENDS ReachabilityAlg, ReachabilityLemmas, Naturals, Sequences, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
INIT ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

(* ----------------------------------------------------------------------
   Next-state relation (a placeholder for the actual algorithm)
   ---------------------------------------------------------------------- *)
NEXT ==
  \/ /\ pc = "start"
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A n \in marked :
        \A m \in Succ[n] : m \in marked \/ m \in frontier

Inv2 ==
  /\ marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Inv3 ==
  /\ Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == {Inv1, Inv2, Inv3}

(* ----------------------------------------------------------------------
   Partial‑correctness property (theorem)
   ---------------------------------------------------------------------- *)
PROPERTIES ==
  /\ pc = "done"
     => marked = Reachable({Root})

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec ==
  /\ INIT
  /\ [][NEXT]_<<marked, frontier, pc>>

====