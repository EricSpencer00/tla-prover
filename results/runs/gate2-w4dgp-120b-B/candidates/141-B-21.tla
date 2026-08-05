---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  It is   *)
(* based on an algorithm by J. Misra that is a variant of breadth-first     *)
(* search.  The algorithm computes the reachable set by repeatedly adding    *)
(* nodes to the marked set, using a workset vroot of nodes that still need  *)
(* to be explored.                                                          *)
(*                                                                         *)
(* The algorithm is defined in the PlusCal block below and then translated  *)
(* to TLA+.  TLC checking of this module is part of the regression suite     *)
(* for the Reachability module in which the ReachableFrom operator is       *)
(* defined.                                                                 *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

\* This is a faithful translation of the PlusCal block at the end of the   *
\* module.  It implements Misra's algorithm, in which vroot and marked     *
\* need not stay disjoint.                                                *
a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot :
                    IF v \notin marked
                       THEN /\ marked' = marked \cup {v}
                            /\ vroot' = vroot \cup Succ[v]
                       ELSE /\ marked' = marked
                            /\ vroot' = vroot \ {v}
                /\ UNCHANGED pc
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

\* Once the algorithm has halted it is allowed to stutter forever, so it  *
\* never deadlocks on termination.                                        *
Quiesce == (pc = "Done") /\ UNCHANGED vars

Next == a \/ Quiesce

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

Termination == <>(pc = "Done")

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

\* Each reachable node is either already marked, or reachable from some  *
\* still-unexplored node in vroot.                                         *
Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)
        /\ (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)
        /\ Reachable = marked \cup ReachableFrom(vroot)

TypeOKInv == TypeOK /\ Inv1

=============================================================================