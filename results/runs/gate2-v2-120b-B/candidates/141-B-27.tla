---- MODULE Reachable ----
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.        *)
(* The purpose of the algorithm is to compute Reachable.                  *)
(***************************************************************************)
Reachable == ReachableFrom({Root})
---------------------------------------------------------------------------
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initialization of the algorithm.                                        *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(***************************************************************************)
(* Action a implements Misra's variant of the breadth‑first search.        *)
(* The subtle point is that when the branch where v \in marked is taken,   *)
(* the variable pc must remain unchanged; otherwise TLC reports that pc   *)
(* is not assigned in that branch.                                         *)
(***************************************************************************)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>
          ELSE
              /\ \E v \in vroot:
                     IF v \notin marked
                        THEN /\ marked' = marked \cup {v}
                             /\ vroot'  = vroot \cup Succ[v]
                             /\ pc' = "a"
                        ELSE /\ marked' = marked
                             /\ vroot'  = vroot \ {v}
                             /\ pc' = "a"
                /\ UNCHANGED pc

Terminate ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    a \/ Terminate

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)

Termination == <>[pc = "Done"]_<<pc>>

(***************************************************************************)
(* Type correctness invariant.                                            *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* First invariant: each node's successors stay within marked ∪ vroot.    *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Second invariant: the set reachable from vroot together with marked   *)
(* equals the reachable set from their union.                             *)
(***************************************************************************)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Third invariant: the algorithm maintains the relationship between      *)
(* the computed set and the specification's Reachable.                    *)
(***************************************************************************)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem – when the algorithm terminates,          *)
(* marked equals Reachable.                                               *)
(***************************************************************************)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================