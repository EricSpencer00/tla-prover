---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root *)
Reachable == ReachableFrom({Root})

(*--------------------------------------------------------------------*)
(* Variables *)
VARIABLES marked, vroot, pc

(* Convenience tuple of all variables *)
vars == << marked, vroot, pc >>

(*--------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(*--------------------------------------------------------------------*)
(* Action a: implements Misra's variant of the BFS algorithm *)
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
                     ELSE /\ marked' = marked
                          /\ vroot' = vroot \ {v}
                          /\ pc' = "a"

(*--------------------------------------------------------------------*)
(* Allow infinite stuttering after termination to avoid deadlock *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

(*--------------------------------------------------------------------*)
(* Full specification *)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------*)
(* Temporal properties *)
Termination == <> (pc = "Done")

(*--------------------------------------------------------------------*)
(* Type correctness invariant *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(*--------------------------------------------------------------------*)
(* Invariant capturing the relationship between marked and vroot *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(*--------------------------------------------------------------------*)
(* Reachability invariant *)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(*--------------------------------------------------------------------*)
(* Convenience invariant linking Reachable to the variables *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(*--------------------------------------------------------------------*)
(* Partial correctness theorem (stated as an invariant for TLC) *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

=============================================================================