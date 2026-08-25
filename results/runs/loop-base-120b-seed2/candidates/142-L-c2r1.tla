---- MODULE ReachableProofs ----
EXTENDS TLC

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(*--------------------------------------------------------------------
  ASSUMPTIONS ABOUT EXTERNAL DEFINITIONS
--------------------------------------------------------------------*)
(* Successor relation: for each node a (possibly empty) set of its successors *)
ASSUME Succ \in [Nodes -> SUBSET Nodes]

(* Reachability operator: maps a set of nodes to the set of nodes reachable
   from it via the successor relation.  Its precise definition is supplied
   elsewhere (e.g., in the ReachabilityLemmas module).  Here we treat it as
   an uninterpreted function with the appropriate type. *)
ASSUME Reachable \in [SUBSET Nodes -> SUBSET Nodes]

(*--------------------------------------------------------------------
  INITIAL STATE
--------------------------------------------------------------------*)
Init ==
    TRUE

(*--------------------------------------------------------------------
  NEXT STATE RELATION
--------------------------------------------------------------------*)
Next ==
    \/ UNCHANGED <<Marked, Frontier, pc>>

(*--------------------------------------------------------------------
  INVARIANTS
--------------------------------------------------------------------*)
(* Invariant 1: type correctness and every successor of a marked node
   is either already marked or in the frontier. *)
Invariant1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(* Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier) *)
Invariant2 ==
    (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

(* Invariant 3: reachable from the root = marked ∪ reachable(frontier) *)
Invariant3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

Invariants ==
    /\ Invariant1
    /\ Invariant2
    /\ Invariant3

(*--------------------------------------------------------------------
  PROPERTIES (used by TLAPS proofs)
--------------------------------------------------------------------*)
Properties ==
    << Invariant1, Invariant2, Invariant3 >>

(*--------------------------------------------------------------------
  SPECIFICATION
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<Marked, Frontier, pc>>

====