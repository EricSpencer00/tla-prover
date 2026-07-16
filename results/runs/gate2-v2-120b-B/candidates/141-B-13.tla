---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  It is, to my knowledge, a new       *)
(* variant of a fairly obvious breadth‑first search for reachable nodes.   *)
(* It is easier to implement using multiple processors than the obvious    *)
(* algorithm.  Module ParReach describes such an implementation.            *)
(*                                                                         *)
(* The module ReachableProofs contains a TLA+ proof of the algorithm’s    *)
(* safety property (partial correctness).  TLAPS has checked those        *)
(* proofs.                                                                 *)
(*                                                                         *)
(* Reachability is expressed via the operator ReachableFrom defined in    *)
(* module Reachability, which describes a directed graph using the          *)
(* constants Nodes and Succ, where Succ[m] is the set of successors of m.   *)
(***************************************************************************)

EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is the set of nodes reachable from Root.                      *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

(***************************************************************************)
(* Initialization.                                                        *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ vroot  = {Root}
    /\ pc     = "a"

(***************************************************************************)
(* One iteration of the algorithm, faithfully reflecting the PlusCal code. *)
(* The action is split into the case where v is already marked (in which   *)
(* case it is removed from vroot) and the case where v is not marked      *)
(* (in which case v is added to marked and all its successors are added   *)
(* to vroot).  The variable pc is left unchanged, because the algorithm    *)
(* stays in the same control state until termination.                     *)
(***************************************************************************)
a ==
    /\ pc = "a"
    /\ vroot /= {}
    /\ \E v \in vroot :
          IF v \notin marked
             THEN /\ marked' = marked \cup {v}
                  /\ vroot'  = vroot \cup Succ[v]
                  /\ pc'     = "a"
             ELSE /\ vroot' = vroot \ {v}
                  /\ marked' = marked
                  /\ pc'    = "a"
    /\ UNCHANGED << >>

(***************************************************************************)
(* When vroot becomes empty, the algorithm moves to the terminating state. *)
(***************************************************************************)
Terminate ==
    /\ pc = "a"
    /\ vroot = {}
    /\ pc' = "Done"
    /\ UNCHANGED << marked, vroot >>

(***************************************************************************)
(* Allow stuttering after termination to avoid deadlock.                  *)
(***************************************************************************)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ a
    \/ Terminate
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(a)          \* weak fairness of the substantive computation

Termination == <>(pc = "Done")

(***************************************************************************)
(* Type correctness invariant.                                            *)
(***************************************************************************)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(***************************************************************************)
(* Invariant used in the original development.                            *)
(***************************************************************************)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

=============================================================================