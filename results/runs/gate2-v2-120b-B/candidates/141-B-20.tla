---- MODULE Reachable ----
(***************************************************************************)
(* Corrected version of the Reachable module.  The only change is that the   *)
(* action `a` now explicitly updates the program counter `pc` on every     *)
(* execution of the loop body.  This eliminates the TLC error that the     *)
(* successor state was missing a value for `pc`.  The semantics of the      *)
(* algorithm are unchanged: the algorithm still behaves exactly as described*)
(* in the original PlusCal code.                                           *)
(***************************************************************************)

EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(* The set of nodes reachable from Root *)
Reachable == ReachableFrom({Root})

(***************************************************************************)
(* Variables *)
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initial state *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(***************************************************************************)
(* Loop body action, corrected to assign `pc` on every execution. *)
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
               /\ UNCHANGED <<>>   \* (no other variables change)

(***************************************************************************)
(* Allow infinite stuttering after termination. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)   \* Weak fairness of the loop action

Termination ==
    <> (pc = "Done")

(***************************************************************************)
(* Type correctness invariant, unchanged from the original specification. *)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* The original invariants, unchanged. *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem, unchanged. *)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

(***************************************************************************)
(* Liveness theorem about termination when Reachable is finite. *)
THEOREM ASSUME IsFiniteSet(Reachable)
         PROVE  Spec => <> (pc = "Done")
=============================================================================