---- MODULE Reachable ----
\* This module implements Misra's variant of a breadth-first search that
\* computes the set of nodes reachable from a given node Root in a directed
\* graph.  The variant keeps the set of marked nodes and the set of nodes
\* in the search frontier (vroot) separate, so a marked node may still
\* appear in vroot and cause its successors to be re-added to vroot even
\* after it has been marked.  The algorithm terminates when vroot is empty.
\* The invariants below capture the relationship between the marked nodes
\* and the frontier nodes that is essential to the algorithm's correctness.
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssump == Root \in Nodes

(***************************************************************************)
(* Reachable is the set of nodes reachable from Root in the graph described *)
(* by Reachability.  The algorithm computes exactly this set in `marked'.  *)
(***************************************************************************)
Reachable == ReachableFrom({Root})

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
                        ELSE /\ marked' = marked
                             /\ vroot' = vroot \ {v}
               /\ pc' = "a"

\* Allow infinite stuttering once the algorithm has terminated.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}

Inv1 == /\ TypeOK
        /\ \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

(***************************************************************************)
(* This is the key invariant: every node reachable from the frontier is   *)
(* reachable from the marked nodes together with the frontier.  Because    *)
(* bfsToRight never adds nodes that are not reachable from vroot, the left *)
(* hand side equals the full reachable set reachable from marked, which is *)
(* how the algorithm eventually terminates.  Inv2 is preserved because each   *)
(* `a' step either adds one node to marked and at most its successors to   *)
(* vroot, or removes one vroot node that is already in marked.            *)
(***************************************************************************)
Inv2 == (marked \cup ReachableFrom(vroot)) = ReachableFrom(marked \cup vroot)

Inv3 == Reachable = marked \cup ReachableFrom(vroot)

TypeOKInv1 == TypeOK /\ Inv1

TypeOKInv2 == TypeOK /\ Inv2

TypeOKInv3 == TypeOK /\ Inv3

TypeOKInv3TypeOK == Inv3 => TypeOK

(***************************************************************************)
(* Partial correctness: at termination (pc = "Done") the marked set is the *)
(* full reachable set.                                                      *)
(***************************************************************************)
PartialCorrectness == (pc = "Done") => (marked = Reachable)

(***************************************************************************)
(* Termination: if the reachable set is finite, the frontier eventually   *)
(* empties and the algorithm terminates.                                     *)
(***************************************************************************)
Termination == (IsFiniteSet(Reachable) /\ Spec) ~> (pc = "Done")

====