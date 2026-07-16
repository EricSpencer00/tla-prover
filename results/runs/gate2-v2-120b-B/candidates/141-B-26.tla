---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  The   *)
(* algorithm is due to Jayadev Misra.  It is, to my knowledge, a new       *)
(* variant of a fairly obvious breadth-first search for reachable nodes.   *)
(* I find this algorithm interesting because it is easier to implement     *)
(* using multiple processors than the obvious algorithm.  Module ParReach  *)
(* describes such an implementation.  You may want to read it after        *)
(* reading this module.                                                    *)
(*                                                                         *)
(* Module ReachableProofs contains a TLA+ proof of the algorithm's safety  *)
(* property--that is, partial correctness, which means that if the         *)
(* algorithm terminates then it produces the correct answer.  That proof   *)
(* has been checked by TLAPS, the TLA+ proof system.  The proof is based   *)
(* on ideas from an informal correctness proof by Misra.                   *)
(*                                                                         *)
(* In this module, reachability is expressed in terms of the operator      *)
(* ReachableFrom, where ReachableFrom(S) is the set of nodes reachable     *)
(* from the nodes in the set S of nodes.  This operator is defined in      *)
(* module Reachability.  That module describes a directed graph in terms   *)
(* of the constants Nodes and Succ, where Nodes is the set of nodes and    *)
(* Succ is a function with domain Nodes such that Succ[m] is the set of    *)
(* all nodes n such that there is an edge from m to n.  If you are not     *)
(* familiar with directed graphs, you should read at least the opening     *)
(* comments in module Reachability.                                        *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is defined to be the set of nodes reachable from Root.  The   *)
(* purpose of the algorithm is to compute Reachable.                       *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, vroot, pc

\* Helper tuple for stuttering (to keep the same shape as the original spec)
vars == << marked, vroot, pc >>

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

\* ----------------------------------------------------------------------
\* Action 'a' – implements Misra's variant of the breadth‑first search
\* ----------------------------------------------------------------------
a ==
    /\ pc = "a"
    /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot:
                /\ IF v \notin marked
                      THEN /\ marked' = marked \cup {v}
                           /\ vroot' = vroot \cup Succ[v]
                      ELSE /\ marked' = marked
                           /\ vroot' = vroot \ {v}
               /\ pc' = "a"

\* ----------------------------------------------------------------------
\* Allow infinite stuttering to prevent deadlock on termination
\* ----------------------------------------------------------------------
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Liveness condition (used in the theorems, not in the model)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Type correctness invariant (unchanged from the original)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

\* ----------------------------------------------------------------------
\* Invariant Inv1 – the original second conjunct is unchanged
\* ----------------------------------------------------------------------
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

\* ----------------------------------------------------------------------
\* Invariant Inv2 – unchanged
\* ----------------------------------------------------------------------
Inv2 ==
    (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

\* ----------------------------------------------------------------------
\* Invariant Inv3 – unchanged
\* ----------------------------------------------------------------------
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

\* ----------------------------------------------------------------------
\* Partial correctness theorem (unchanged)
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => (marked = Reachable)

THEOREM Spec => []PartialCorrectness

\* ----------------------------------------------------------------------
\* Termination theorem (unchanged)
\* ----------------------------------------------------------------------
THEOREM  ASSUME IsFiniteSet(Reachable)
         PROVE  Spec => <>(pc = "Done")

=============================================================================