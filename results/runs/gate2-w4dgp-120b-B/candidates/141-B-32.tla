---- MODULE Reachable
(***************************************************************************)
(* This module specifies an algorithm for computing the set of nodes in a  *)
(* directed graph that are reachable from a given node called Root.  It is   *)
(* a breadth-first search variant due to Jayadev Misra.  The algorithm is   *)
(* captured in the PlusCal block below, which is followed by its TLA+        *)
(* translation.  Two invariants of the translation together imply partial   *)
(* correctness: on termination, the set `marked' equals the full reachable  *)
(* set.  A liveness theorem asserts that, because the reachable set is      *)
(* finite, the algorithm always eventually terminates.                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Reachability

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

Reachable == ReachableFrom({Root})

\* BEGIN TRANSLATION
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init == /\ marked = {}
        /\ vroot = {Root}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF vroot = {}
          THEN /\ pc' = "Done"
               /\ UNCHANGED << marked, vroot >>
          ELSE /\ \E v \in vroot :
                    /\ IF v \notin marked
                         THEN /\ marked' = marked \cup {v}
                              /\ vroot' = vroot \cup Succ[v]
                         ELSE /\ vroot' = vroot \ {v}
                              /\ UNCHANGED marked
               /\ UNCHANGED pc

Next == a

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")
\* END TRANSLATION

\* Invariants: the graph-theoretic claim about reachable nodes (Inv3) and
\* a well-typedness claim that also keeps pc = "Done" from being reachable
\* before vroot is empty (TypeOK).
TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}
          /\ (pc = "Done") => (vroot = {})

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

THEOREM Spec => [](pc = "Done" => marked = Reachable)

\* The reachable set is finite in every model we consider (FiniteNodes), and
\* fairness of the single action forces termination.
ASSUME FiniteNodes == (\A n \in Nodes : Cardinality(Succ[n]) <= 2)
ASSUME Finite == IsFiniteSet(Reachable)
ASSUME Fairness == WF_vars(a)

THEOREM Spec /\ Fairness /\ Finite => Termination

=============================================================================