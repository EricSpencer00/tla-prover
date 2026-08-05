---- MODULE Reachable
EXTENDS Reachability, Integers, FiniteSets

CONSTANT Root
ASSUME RootAssume == Root \in Nodes

\* Reachable is the set of nodes reachable from node Root.
Reachable == ReachableFrom({Root})

\* The algorithm's variables:  marked is the set of nodes known to be
\* reachable; vroot is the set of nodes that may still add to marked.
VARIABLES marked, vroot, pc

vars == << marked, vroot, pc >>

Init ==
  /\ marked = {}
  /\ vroot = {Root}
  /\ pc = "a"

\* Action a is the algorithm's only step.  It is chosen by a fair
\* scheduler, which is what lets it finish even though it may keep
\* revisiting nodes already in marked.
a ==
  /\ pc = "a"
  /\ \/ /\ vroot = {}
        /\ pc' = "Done"
        /\ UNCHANGED << marked, vroot >>
     \/ \E v \in vroot:
          /\ marked' = IF v \in marked THEN marked ELSE marked \cup {v}
          /\ vroot'  = vroot \cup IF v \in marked THEN {} ELSE Succ[v]
          /\ pc' = "a"

\* The algorithm idles once it has completed; this is the stuttering
\* that makes the state graph strongly connected for TLC's graph search.
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(a)

\* Invariant: a node's successors are always in marked or in vroot,
\* so no reachable node is ever dropped from consideration.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup vroot)

\* Invariant: the nodes reachable from marked together with those
\* reachable from vroot are exactly the nodes reachable from their union.
Inv2 == marked \cup ReachableFrom(vroot) = ReachableFrom(marked \cup vroot)

\* Because Root is the only node in vroot initially, the reachable nodes
\* are exactly marked together with the nodes reachable from vroot.
Inv3 == Reachable = marked \cup ReachableFrom(vroot)

TypeOK == /\ marked \in SUBSET Nodes
          /\ vroot \in SUBSET Nodes
          /\ pc \in {"a", "Done"}

TerminatingCorrectness ==
  (pc = "Done") => (marked = Reachable)

THEOREM Spec => []TerminatingCorrectness

\* If the reachable set is finite, the algorithm reaches its idle
\* state, since a fair scheduler cannot keep it busy forever.
FairTermination == Spec => (Reachable # {} => <>(pc = "Done"))

====