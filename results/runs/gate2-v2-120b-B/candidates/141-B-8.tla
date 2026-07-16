---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(* Initial state: marked empty, vroot contains only Root, pc = "a" *)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* Action a: choose a node v from vroot and either add it to marked and
   expand vroot with its successors, or remove it from vroot if it is
   already marked.  pc remains "a". *)
A ==
    /\ pc = "a"
    /\ vroot # {}
    /\ \E v \in vroot:
          IF v \notin marked THEN
              /\ marked' = marked \cup {v}
              /\ vroot'  = vroot \cup Succ[v]
          ELSE
              /\ marked' = marked
              /\ vroot'  = vroot \ {v}
    /\ pc' = "a"

(* Termination step: when vroot is empty, set pc to "Done". *)
Terminating ==
    /\ pc = "a"
    /\ vroot = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, vroot >>

(* Stuttering step to avoid deadlock after termination. *)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ A
    \/ Terminating
    \/ Stutter

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(A)      \* Weak fairness for the main action

Termination == <> (pc = "Done")

(***************************************************************************)
(* Type correctness invariant.                                            *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Inv1: the successors of any marked node are in marked or vroot.        *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Inv2: reachable nodes from marked ∪ vroot equal reachable nodes from   *)
(* the union of those sets.                                                *)
(***************************************************************************)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Inv3: the algorithm's computed set equals the actual reachable set.    *)
(***************************************************************************)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem: when the algorithm terminates, marked   *)
(* equals the set of all nodes reachable from Root.                        *)
(***************************************************************************)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

=============================================================================