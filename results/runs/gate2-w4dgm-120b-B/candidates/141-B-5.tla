----------------------------- MODULE Reachable -----------------------------
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  I find this algorithm interesting   *)
(* because it is easier to implement using multiple processors than the     *)
(* obvious algorithm.  Module ParReach describes such an implementation.  *)
(*                                                                         *)
(* Reachable is defined in terms of the operator ReachableFrom, where     *)
(* ReachableFrom(S) is the set of nodes reachable from the set S of nodes. *)
(* This operator is defined in module Reachability, which describes the    *)
(* directed graph by the constants Nodes and Succ.  If you are not familiar *)
(* with directed graphs, read its opening comments.                        *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of notes reachable from Root.  The   *)
(* purpose of the algorithm is to compute Reachable.                       *)
(***************************************************************************)
Reachable == ReachableFrom({Root})
---------------------------------------------------------------------------
(***************************************************************************
The obvious algorithm for Reachable is a breadth-first search with two
variables, `marked' and vroot.  Misra's variant differs in that `marked'
and vroot need not be disjoint: while vroot is nonempty it chooses a node
and, if the node is not yet marked, adds it to `marked' and adds ALL of
its successors to vroot, not just the unmarked ones.  If the node is
already marked it is removed from vroot.  The algorithm terminates when
vroot is empty, and at that point `marked' = Reachable.
***************************************************************************)

\* BEGIN TRANSLATION    Here is the TLA+ translation of the PlusCal code.
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == (* Global variables *)
        /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot /= {}
           THEN /\ \E v \in vroot:
                     IF v \notin marked
                        THEN /\ marked' = (marked \cup {v})
                             /\ vroot'  = (vroot \cup Succ[v])
                        ELSE /\ vroot' = vroot \ {v}
                             /\ UNCHANGED marked
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << marked, vroot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
----------------------------------------------------------------------------
(***************************************************************************)
(* Partial correctness is based on these invariants.                       *)
(***************************************************************************)
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})
  (*************************************************************************)
  (* The invariance of TypeOK is obvious.  (I made the fact that pc = "Done" *)
  (* only when vroot = {} part of the type-correctness invariant.)         *)
  (*************************************************************************)

Inv1 == /\ TypeOK  
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)
  (*************************************************************************)
  (* Each element of Succ[n] is added to vroot when n is added to `marked', *)
  (* so it stays in vroot until it too is added to `marked'.                *)
  (*************************************************************************)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)
  (*************************************************************************)
  (* Since ReachableFrom(marked \cup vroot) is the union of                *)
  (* ReachableFrom(marked) and ReachableFrom(vroot), to prove Inv2 is     *)
  (* invariant we must show ReachableFrom(marked) is a subset of           *)
  (* marked \cup ReachableFrom(vroot).  A node m in ReachableFrom(marked) *)
  (* has a path from some p in `marked'; the first node on that path not   *)
  (* already in `marked' is reachable from vroot, so m is in the RHS.      *)
  (*************************************************************************)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)
  (*************************************************************************)
  (* Let R = marked \cup ReachableFrom(vroot).  Each action either adds  *)
  (* a node to both `marked' and ReachableFrom(vroot) (case 1) or moves a *)
  (* node from ReachableFrom(vroot) to `marked' (case 2), so R is         *)
  (* unchanged.                                                            *)
  (*************************************************************************)

PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness
  (*************************************************************************)
  (* From TypeOK, (pc = "Done") => (vroot = {}); ReachableFrom({}) = {};  *)
  (* Inv3 then gives (vroot = {}) => (marked = Reachable).                *)
  (*************************************************************************)

(***************************************************************************)
(* If Reachable is finite, the algorithm eventually terminates.            *)
(***************************************************************************)
THEOREM  ASSUME IsFiniteSet(Reachable)
         PROVE  Spec => <>(pc = "Done")
  (*************************************************************************)
  (* From TypeOK, (pc = "Done") => (vroot = {}), so we need <>(vroot = {}).*)
  (* Assume instead [](vroot # {}); since PC stays in {"a","Done"}, WF of    *)
  (* `a' gives infinitely many `a' steps.  Inv3 and finiteness of Reachable *)
  (* bound the size of `marked' and vroot, so infinitely many `a' steps     *)
  (* imply infinitely many distinct nodes added to `marked', impossible.     *)
  (*************************************************************************)

 (**************************************************************************)
 (* TLC can check these on small graphs.                                   *)
 (**************************************************************************)
=============================================================================