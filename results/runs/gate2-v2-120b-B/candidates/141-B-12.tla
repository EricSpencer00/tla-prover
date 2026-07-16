---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* Reachable is defined to be the set of nodes reachable from Root. *)
Reachable == ReachableFrom({Root})

(*-------------------------------------------------------------------*)
(* Variables *)
VARIABLES marked, vroot, pc

(*-------------------------------------------------------------------*)
(* Helper definition for the tuple of variables *)
vars == << marked, vroot, pc >>

(*-------------------------------------------------------------------*)
(* Initial predicate *)
Init ==
    /\ marked = {}
    /\ vroot  = {Root}
    /\ pc     = "a"

(*-------------------------------------------------------------------*)
(* Action a, faithfully reflecting the PlusCal algorithm *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot:
                   IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot'  = vroot \cup Succ[v]
                      ELSE /\ marked' = marked
                           /\ vroot'  = vroot \ {v}
               /\ pc' = "a"

(*-------------------------------------------------------------------*)
(* Allow infinite stuttering after termination *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

(*-------------------------------------------------------------------*)
(* Specification *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

(*-------------------------------------------------------------------*)
(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(*-------------------------------------------------------------------*)
(* Safety invariants *)

Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(*-------------------------------------------------------------------*)
(* Partial correctness theorem *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================