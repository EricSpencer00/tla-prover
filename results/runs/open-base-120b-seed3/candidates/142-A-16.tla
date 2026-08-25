---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Definitions taken from the sequential reachability algorithm.
-----------------------------------------------------------------*)
(* The algorithm uses the function Succ : Nodes -> SUBSET Nodes
   and the operator ReachFrom : SUBSET Nodes -> SUBSET Nodes
   which are provided by the extended modules. *)

(*-----------------------------------------------------------------
  INITIAL STATE
-----------------------------------------------------------------*)
INIT ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

(*-----------------------------------------------------------------
  NEXT STATE RELATION
-----------------------------------------------------------------*)
NEXT ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            LET newFrontier == (frontier \ {n}) \cup (Succ[n] \ marked)
            IN
               /\ marked' = marked \cup {n}
               /\ frontier' = newFrontier
               /\ pc' = "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

(*-----------------------------------------------------------------
  SPECIFICATION
-----------------------------------------------------------------*)
Spec ==
    INIT /\ [][NEXT]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  INVARIANTS
-----------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Succ[n] : s \in marked \/ s \in frontier

Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(*-----------------------------------------------------------------
  PROPERTIES (partial correctness theorem)
-----------------------------------------------------------------*)
PartialCorrectness ==
    /\ pc = "done"
    => marked = ReachFrom({Root})

PROPERTIES == PartialCorrectness

====