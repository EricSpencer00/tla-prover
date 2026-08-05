---- MODULE Reachable
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  It is  *)
(* a breadth-first search and a variant of one described by Jayadev Misra. *)
(* The module contains the algorithm, its safety invariant, a partial     *)
(* correctness theorem, and a termination theorem conditional on the      *)
(* reachable set being finite.                                             *)
(***************************************************************************)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

\* Reachable is the set of nodes reachable from Root.
Reachable == ReachableFrom({Root})

\* A breadth-first search with two queues: marked (done) and vroot (todo).
VARIABLES marked, vroot, pc
vars == << marked, vroot, pc >>

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

\* The step: add a node's successors to vroot and the node to marked, or
\* discard a node already in marked.
a == /\ pc = "a"
     /\ IF vroot /= {}
          THEN /\ \E v \in vroot :
                   /\ IF v \notin marked
                        THEN /\ marked' = marked \cup {v}
                             /\ vroot' = vroot \cup Succ[v]
                        ELSE /\ vroot' = vroot \ {v}
                             /\ marked' = marked
                /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>

Stutter == pc = "Done" /\ UNCHANGED vars
Next == a \/ Stutter
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

\* Invariant: everything in a marked node's successor set is reachable.
Inv1 == /\ marked \cup ReachableFrom(vroot) = ReachableFrom(marked \cup vroot)
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == Reachable = marked \cup ReachableFrom(vroot)
InvState == TypeOK /\ Inv1 /\ Inv2

Termination == <>(pc = "Done")

TypeOKInv == Spec => []TypeOK
Inv1Inv == Spec => []Inv1
Inv2Inv == Spec => []Inv2

\* Partial correctness: on termination, marked = Reachable.
PartialCorrectness == (pc = "Done") => (marked = Reachable)

\* If the reachable set is finite the search eventually terminates.
\* Termination depends on weak fairness of action a.
TerminationTheorem == (IsFiniteSet(Reachable)) => (Spec => Termination)

=============================================================================