---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

(*---------------------------------------------------------------------*)
(*  Constants (to be supplied by the .cfg)                             *)
(*---------------------------------------------------------------------*)
CONSTANTS Nodes, Root, Succ, Seq

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                *)
(*---------------------------------------------------------------------*)
Node == Nodes

(* Succ is a function from a node to its set of successors. *)
SuccSet == [n \in Nodes |-> Succ[n]]

(* ReachableFrom: the set of nodes reachable from a given set via Succ. *)
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN
       S \cup ReachableFrom(SuccSet[n] \cup (S \ {n}))

(* ReachableFromRoot is the set of all nodes reachable from the root. *)
ReachableFromRoot == ReachableFrom({Root})

(*---------------------------------------------------------------------*)
(*  Variables                                                         *)
(*---------------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*---------------------------------------------------------------------*)
(*  Types and type correctness invariant                               *)
(*---------------------------------------------------------------------*)
TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"Running", "Done"}

(*---------------------------------------------------------------------*)
(*  Initial state                                                     *)
(*---------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Running"

(*---------------------------------------------------------------------*)
(*  Actions                                                           *)
(*---------------------------------------------------------------------*)
PickFrontierNode == CHOOSE n \in frontier : TRUE

MarkAndExpand ==
  /\ pc = "Running"
  /\ LET n == PickFrontierNode IN
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup SuccSet[n]
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Running"

RemoveMarkedFromFrontier ==
  /\ pc = "Running"
  /\ LET n == PickFrontierNode IN
        /\ n \in marked
        /\ frontier' = frontier \ {n}
        /\ marked' = marked
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Running"

Terminate ==
  /\ pc = "Done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == \/ MarkAndExpand
        \/ RemoveMarkedFromFrontier
        \/ Terminate

(*---------------------------------------------------------------------*)
(*  Specification                                                     *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*---------------------------------------------------------------------*)
(*  Invariants                                                         *)
(*---------------------------------------------------------------------*)
(* Inv1: every successor of a marked node is in marked or frontier *)
Inv1 == \A n \in marked : SuccSet[n] \subseteq marked \cup frontier

(* Inv2: union of marked and nodes reachable from frontier equals
        nodes reachable from the union of marked and frontier *)
Inv2 == ReachableFrom(marked \cup frontier) = marked \cup
        ReachableFrom(frontier)

(* Inv3: nodes reachable from root equal marked plus nodes reachable from frontier *)
Inv3 == ReachableFromRoot = marked \cup ReachableFrom(frontier)

(* Partial correctness: when terminated, marked = reachable from root *)
PartialCorrectness ==
  /\ pc = "Done"
  /\ marked = ReachableFromRoot

(*---------------------------------------------------------------------*)
(*  Liveness property (termination)                                   *)
(*---------------------------------------------------------------------*)
Termination == <>[pc = "Done"]_<<pc>>

(*---------------------------------------------------------------------*)
(*  THEOREMS (optional, to expose invariants to TLC)                   *)
(*---------------------------------------------------------------------*)
THEOREM TypeOK => []TypeOK
THEOREM Inv1 => []Inv1
THEOREM Inv2 => []Inv2
THEOREM Inv3 => []Inv3
THEOREM PartialCorrectness => []PartialCorrectness
THEOREM Termination => <>[pc = "Done"]_<<pc>>

=============================================================================