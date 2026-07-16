---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.       *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

(***************************************************************************)
(* Translation of the PlusCal algorithm.                                   *)
(***************************************************************************)

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = "a"

(* Action a: the core step of the algorithm. *)
a ==
  /\ pc = "a"
  /\ IF vroot = {}
       THEN /\ pc' = "Done"
            /\ UNCHANGED << marked, vroot >>
       ELSE
         /\ \E v \in vroot :
               IF v \notin marked
                  THEN /\ marked' = marked \cup {v}
                       /\ vroot' = vroot \cup Succ[v]
                       /\ pc' = "a"
                  ELSE /\ marked' = marked
                       /\ vroot' = vroot \ {v}
                       /\ pc' = "a"
         /\ UNCHANGED pc

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ a
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(a)

Termination ==
  <> (pc = "Done")

(***************************************************************************)
(* Invariant used for type checking.                                       *)
(***************************************************************************)
TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ vroot \in SUBSET Nodes
  /\ pc \in {"a", "Done"}
  /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Safety invariant: every node in `marked` has all its successors either   *)
(* in `marked` or in `vroot`.                                               *)
(***************************************************************************)
Inv1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Relates `marked` and `vroot` to the reachability operator.               *)
(***************************************************************************)
Inv2 ==
  (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Connects the algorithm's state to the specification's intent.          *)
(***************************************************************************)
Inv3 ==
  Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness ==
  (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================