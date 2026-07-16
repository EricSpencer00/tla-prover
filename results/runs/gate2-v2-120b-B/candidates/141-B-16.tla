---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

(***************************************************************************)
(* Variables for Misra's variant of the breadth‑first search algorithm.    *)
(***************************************************************************)
VARIABLES marked, vroot, pc

(* A convenient tuple of all mutable variables *)
vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initial state: nothing is marked, the frontier contains only Root, and  *)
(* the control variable pc indicates that we are in the loop body "a".     *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot  = {Root}
    /\ pc     = "a"

(***************************************************************************)
(* Action a – the body of the while‑loop.                                   *)
(*   * If vroot is empty, we move to the terminating control state "Done".  *)
(*   * Otherwise we nondeterministically pick a node v from vroot.        *)
(*     – If v is not yet marked, we add it to marked and add all its      *)
(*       successors to vroot (the union may already contain them).        *)
(*     – If v is already marked, we simply remove it from vroot.          *)
(*   * The control variable stays in "a" while the loop continues.        *)
(***************************************************************************)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot:
                 IF v \notin marked
                    THEN /\ marked' = marked \cup {v}
                         /\ vroot'  = vroot \cup Succ[v]
                         /\ pc'     = "a"
                    ELSE /\ marked' = marked
                         /\ vroot'  = vroot \ {v}
                         /\ pc'     = "a"

(***************************************************************************)
(* The terminating stuttering step – required so that the model checker    *)
(* never gets stuck when pc = "Done".                                        *)
(***************************************************************************)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Type correctness invariant – exactly as in the original specification.   *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Inv1 – the original invariant about the relationship between marked,   *)
(* vroot and Succ.                                                          *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Inv2 – the original invariant about ReachableFrom.                       *)
(***************************************************************************)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Inv3 – the original invariant linking the computed set to the desired   *)
(* Reachable set.                                                            *)
(***************************************************************************)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem – unchanged from the original.               *)
(***************************************************************************)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================