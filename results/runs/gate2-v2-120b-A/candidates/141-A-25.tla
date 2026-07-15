---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file.  They are left uninterpreted
  here; the configuration file supplies concrete values.
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc, iter

(*-----------------------------------------------------------------
  Derived constant for the set of all valid nodes (type abbreviation)
-----------------------------------------------------------------*)
AllNodes == Nodes

(*-----------------------------------------------------------------
  Type correctness invariant (used also as a simple sanity check)
-----------------------------------------------------------------*)
TypeOK ==
  /\ marked \subseteq AllNodes
  /\ frontier \subseteq AllNodes
  /\ pc \in {"Running", "Done"}
  /\ iter \in Nat

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Reach(root) == { node \in AllNodes : <<node>> \in Seq(root) }

IsReachableSet(s) == s = Reach(Root)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"
  /\ iter = 0

(*-----------------------------------------------------------------
  Main actions
-----------------------------------------------------------------*)
ProcessUnmarked ==
  /\ pc = "Running"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = "Running"
        /\ iter' = iter + 1

ProcessMarked ==
  /\ pc = "Running"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = "Running"
        /\ iter' = iter + 1

Terminate ==
  /\ pc = "Running"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier, iter>>

Next ==
  \/ ProcessUnmarked
  \/ ProcessMarked
  \/ Terminate
  \/ UNCHANGED <<marked, frontier, pc, iter>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, iter>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
(* 1. Every successor of a marked node is either already marked or in frontier *)
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* 2. Union of marked and reachable from frontier equals reachable from their union *)
Inv2 ==
  Reach(Root) = marked \cup (Reach(frontier) \ marked)

(* 3. Reachable from root equals marked plus reachable from frontier *)
Inv3 == Reach(Root) = marked \cup Reach(frontier)

(* Partial correctness: when terminated, marked equals exactly the reachable set *)
PartialCorrectness ==
  pc = "Done" => marked = Reach(Root)

(*-----------------------------------------------------------------
  Liveness property (termination)
-----------------------------------------------------------------*)
Termination == []<>(pc = "Done")

=============================================================================