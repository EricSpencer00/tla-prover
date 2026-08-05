---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  It is   *)
(* a variant of breadth-first search for reachable nodes, due to Jayadev    *)
(* Misra.  It differs from the obvious algorithm in that the two variables  *)
(* `marked' and vroot, which together represent nodes explored and nodes     *)
(* yet to explore, are allowed to overlap.  When a node v in vroot is not   *)
(* already marked, it is added to marked and its successors are added to     *)
(* vroot, regardless of whether any of them are already in marked.  When a  *)
(* node is already in marked, it is simply removed from vroot.               *)
(*                                                                         *)
(* The algorithm's correctness is captured by three semantic invariants    *)
(* (Inv1-Inv3); the module ReachableProofs contains a TLAPS-checked proof   *)
(* of partial correctness (termination implies the answer is correct) and  *)
(* a detailed informal argument of termination itself.                     *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

(***************************************************************************)
(* Reachable is the set of notes reachable from Root, computed by the       *)
(* algorithm.                                                               *)
(***************************************************************************)
Reachable == ReachableFrom({Root})
---------------------------------------------------------------------------
(***************************************************************************
Obvious algorithm: `marked' and vroot are disjoint.  Misra's variant lets   *)
(* them overlap: while vroot is non-empty, pick v in vroot and either add it  *)
(* to `marked' and add all of Succ[v] to vroot, or (if it is already in     *)
(* `marked') simply remove it from vroot.  This is the PlusCal code:        *)
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot # {}
          THEN /\ \E v \in vroot :
                     IF v \notin marked
                        THEN /\ marked' = marked \cup {v}
                             /\ vroot'  = vroot \cup Succ[v]
                        ELSE /\ vroot' = vroot \ {v}
                             /\ UNCHANGED marked
                /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")
\* END TRANSLATION
---------------------------------------------------------------------------

(***************************************************************************)
(* The invariants below are preserved by every a-step and together imply   *)
(* partial correctness.  Their informal proofs are sketched in            *)
(* ReachableProofs.                                                          *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => vroot = {}

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness

(***************************************************************************)
(* Termination only holds when the reachable set is finite.  The liveness  *)
(* argument in ReachableProofs proves it from this finiteness hypothesis.  *)
(***************************************************************************)
THEOREM  ASSUME IsFiniteSet(Reachable)
         PROVE  Spec => <>(pc = "Done")

=============================================================================