---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* --------------------------------------------------------------------- *)
(* The set of nodes reachable from the distinguished root node.         *)
(* --------------------------------------------------------------------- *)
Reachable == ReachableFrom({Root})

(* --------------------------------------------------------------------- *)
(* Variables of the algorithm.                                          *)
(* --------------------------------------------------------------------- *)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* --------------------------------------------------------------------- *)
(* Initial state.                                                       *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* --------------------------------------------------------------------- *)
(* The body of the algorithm, reflecting the PlusCal description.       *)
(* --------------------------------------------------------------------- *)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot:
                  IF v \notin marked
                     THEN /\ marked' = marked \cup {v}
                          /\ vroot' = vroot \cup Succ[v]
                          /\ pc' = "a"
                     ELSE /\ vroot' = vroot \ {v}
                          /\ UNCHANGED marked
                          /\ pc' = "a"
              /\ UNCHANGED << >>

(* --------------------------------------------------------------------- *)
(* Allow infinite stuttering after termination to avoid deadlock.       *)
(* --------------------------------------------------------------------- *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    a \/ Terminating

(* --------------------------------------------------------------------- *)
(* Specification of the system.                                         *)
(* --------------------------------------------------------------------- *)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Termination == <> (pc = "Done")

(* --------------------------------------------------------------------- *)
(* Type correctness invariant.                                          *)
(* --------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* --------------------------------------------------------------------- *)
(* Invariant 1: local reachability property.                             *)
(* --------------------------------------------------------------------- *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* --------------------------------------------------------------------- *)
(* Invariant 2: relationship between marked, vroot and ReachableFrom.   *)
(* --------------------------------------------------------------------- *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(* --------------------------------------------------------------------- *)
(* Invariant 3: convenience equation linking Reachable and the variables *)
(* --------------------------------------------------------------------- *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* --------------------------------------------------------------------- *)
(* Partial correctness theorem (as an invariant).                     *)
(* --------------------------------------------------------------------- *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================