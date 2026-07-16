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

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(***************************************************************************)
(* Action a: implements Misra's variant of BFS                           *)
(***************************************************************************)
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot :
                 IF v \notin marked
                    THEN /\ marked' = marked \cup {v}
                         /\ vroot' = vroot \cup Succ[v]
                         /\ pc' = "a"
                    ELSE /\ marked' = marked
                         /\ vroot' = vroot \ {v}
                         /\ pc' = "a"

(***************************************************************************)
(* Allow infinite stuttering to prevent deadlock on termination.          *)
(***************************************************************************)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED << marked, vroot, pc >>

Next ==
    \/ a
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)

Termination == <> (pc = "Done")

(***************************************************************************)
(* Type correctness invariant                                             *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Invariant Inv1: ensures successors of marked nodes stay within the     *)
(*                explored frontier                                          *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* Invariant Inv2: relates ReachableFrom of the frontier to the whole set *)
(***************************************************************************)
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

(***************************************************************************)
(* Invariant Inv3: ties the algorithm's result to the specification's    *)
(*                Reachable set                                            *)
(***************************************************************************)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

(***************************************************************************)
(* Partial correctness theorem                                            *)
(***************************************************************************)
PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => [] PartialCorrectness

=============================================================================