---- MODULE Reachable ----
(* Reachability analysis, Misra variant.  This module describes a
   breadth-first search for nodes reachable from a distinguished root
   node, in which two sets of visited nodes need not be kept disjoint. *)
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

(* Reachable is the set of nodes reachable from Root; the algorithm
   computes it in the variable marked. *)
Reachable == ReachableFrom({Root})

VARIABLES marked, vroot, pc
vars == << marked, vroot, pc >>

Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ pc = "a"

(* The algorithm: while vroot is non-empty, pick a node from it.  If the
   node is not yet marked, add it to marked and add *all* of its
   successors to vroot; otherwise remove it from vroot.  vroot is never
   empty when pc = "a", so the step setting pc to "Done" is always
   guarded by vroot being empty. *)
a ==
    /\ pc = "a"
    /\ \/ /\ vroot /= {}
          /\ \E v \in vroot :
               IF v \notin marked
                  THEN /\ marked' = marked \cup {v}
                       /\ vroot' = vroot \cup Succ[v]
                  ELSE /\ vroot' = vroot \ {v}
                       /\ UNCHANGED marked
          /\ pc' = "a"
        \/ /\ vroot = {}
           /\ pc' = "Done"
           /\ UNCHANGED << marked, vroot >>

Next == a

Termination == <>(pc = "Done")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ (pc = "Done") => (vroot = {})

(* Every successor of a marked node is marked or in vroot. *)
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(* Every node reachable from vroot is reachable from marked \cup vroot. *)
Inv2 ==
    marked \cup ReachableFrom(vroot) =
        ReachableFrom(marked \cup vroot)

(* Reaching exactly the nodes reachable from Root from marked and vroot
   together. *)
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

TypeOKInv == TypeOK /\ Inv1 /\ Inv2 /\ Inv3

PartialCorrectness ==
    (pc = "Done") => (marked = Reachable)
SpecInv == Spec /\ []TypeOKInv

====