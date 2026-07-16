---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc
vars == << marked, vroot, pc >>

(* ------------------------------------------------------------------------- *)
(* Initial predicate                                                          *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* ------------------------------------------------------------------------- *)
(* Action a: implements Misra's variant of BFS                               *)
(* ------------------------------------------------------------------------- *)
a ==
    /\ pc = "a"
    /\ IF vroot = {} THEN
          /\ pc' = "Done"
          /\ UNCHANGED << marked, vroot >>
       ELSE
          /\ \E v \in vroot :
                IF v \notin marked THEN
                     /\ marked' = marked \cup {v}
                     /\ vroot'  = vroot \cup Succ[v]
                ELSE
                     /\ marked' = marked
                     /\ vroot'  = vroot \ {v}
          /\ pc' = "a"

(* ------------------------------------------------------------------------- *)
(* Allow infinite stuttering after termination                                *)
(* ------------------------------------------------------------------------- *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminating

Spec ==
    Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                                *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* ------------------------------------------------------------------------- *)
(* Additional invariants (kept unchanged from the original specification)    *)
(* ------------------------------------------------------------------------- *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(* ------------------------------------------------------------------------- *)
(* Partial correctness theorem (kept unchanged)                              *)
(* ------------------------------------------------------------------------- *)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

====