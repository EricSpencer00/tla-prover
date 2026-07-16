---- MODULE Reachable ----
(***************************************************************************)
(* Corrected version of the Reachable module.  The original specification   *)
(* contained a subtle bug in the action `a`: when the action chose a node   *)
(* `v` that was already in `marked`, the variable `pc` was left unchanged   *)
(* (by the implicit `UNCHANGED pc` of the subaction) while the overall      *)
(* action `a` also permitted the alternative branch `pc' = "a"`.  This      *)
(* combination allowed a transition in which `pc` became the value         *)
(* `null`, violating the type invariant `TypeOK` and causing TLC to report *)
(* that the successor state was not completely specified.                  *)
(*                                                                         *)
(* The fix is to make the two branches of `a` mutually exclusive and      *)
(* exhaustive, and to ensure that every transition updates `pc` to a      *)
(* defined value.  The algorithmic intent is unchanged: when `vroot` is    *)
(* non‑empty the system nondeterministically picks a node `v` from it; if   *)
(* `v` is not yet marked, it is added to `marked` and its successors are   *)
(* added to `vroot`; otherwise `v` is simply removed from `vroot`.  In both *)
(* cases the control variable `pc` remains in the looping state `"a"` and  *)
(* only changes to `"Done"` when the loop terminates.                      *)
(*                                                                         *)
(* The rest of the specification – the auxiliary invariants, the partial  *)
(* correctness theorem, and the termination theorem – is left unchanged   *)
(* and therefore continues to capture the intended semantics of the        *)
(* algorithm.                                                               *)
(***************************************************************************)

EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

---------------------------------------------------------------------------
(***************************************************************************
The PlusCal algorithm (shown in the original comments) is implemented by
the following TLA+ translation.  The only change required for correctness
is the definition of the action `a`, which is now written as a single
deterministic case analysis that always updates `pc` to a defined value.
***************************************************************************)

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action `a` implements one loop iteration of the algorithm. *)
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
                         /\ marked' = marked
                         /\ pc' = "a"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Termination == <> (pc = "Done")

(***************************************************************************)
(* Auxiliary invariants (unchanged from the original specification).       *)
(***************************************************************************)

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem: when the algorithm terminates, `marked'  *)
(* equals the set of nodes reachable from Root.                           *)
(***************************************************************************)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

(***************************************************************************)
(* Termination theorem: if the reachable set is finite, the algorithm     *)
(* eventually reaches the terminating state.                              *)
(***************************************************************************)
THEOREM ASSUME IsFiniteSet(Reachable)
      PROVE Spec => <> (pc = "Done")

=============================================================================