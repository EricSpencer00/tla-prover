---- MODULE Reachable ----
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  It is  *)
(* a breadth-first search for reachable nodes and is due to Jayadev Misra. *)
(* The algorithm is slightly unusual in that two frontier-sets may overlap *)
(* and its termination proof is not completely trivial.                     *)
(*                                                                         *)
(* Reachability is expressed in terms of ReachableFrom, which is defined in *)
(* module Reachability: ReachableFrom(S) is the set of nodes reachable from *)
(* the set S of nodes.  Nodes and Succ are imported from Reachability, where *)
(* Succ[m] is the set of nodes n such that there is an edge from m to n.    *)
(*                                                                         *)
(* Invariant Inv3 expresses the key relationship between the variables:     *)
(* Reachable = marked \cup ReachableFrom(vroot).  Roughly, what is already  *)
(* discovered (marked) plus what is still to be discovered (the reachab-   *)
(* le set of the frontier vroot) is exactly the set Reachable we are after. *)
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

(***************************************************************************)
(* A step that adds a node to `marked' also adds its successors to the      *)
(* frontier vroot, even if they are already reachable from the frontier.   *)
(* When a node in vroot is already in `marked', the step simply removes it. *)
(***************************************************************************)
a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot:
                    /\ marked' = IF v \notin marked
                                   THEN marked \cup {v}
                                   ELSE marked
                    /\ vroot' = IF v \notin marked
                                   THEN vroot \cup Succ[v]
                                   ELSE vroot \ {v}
                /\ pc' = "a"
          ELSE /\ pc' = "Done" /\ UNCHANGED << marked, vroot >>

\* Allow infinite stuttering to prevent a deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(a)

Termination == <>(pc = "Done")

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

\* Partial correctness: on termination, marked equals Reachable.
PartialCorrectness == (pc = "Done") => (marked = Reachable)
THEOREM Spec => []PartialCorrectness

\* The algorithm terminates whenever the reachable set is finite.
THEOREM ASSUME IsFiniteSet(Reachable) PROVE Spec => <>(pc = "Done")
=============================================================================