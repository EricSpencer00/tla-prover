---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* A model-checking configuration module for the sequential Misra reachability
\* algorithm. It inherits the algorithm's state variables and actions, and adds
\* concrete configuration bindings -- a fixed graph and a bounded sequence
\* override -- so the reachable state space is finite and checkable.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

\* Invariant: every marked node has a successor also marked (except a sink),
\* so the marked region is closed under the graph's edges.
Inv1 ==
  \A x \in marked : (ConnectedToSomeButNotAll[x] = {}) \/ (\E y \in ConnectedToSomeButNotAll[x] : y \in marked)

\* Invariant: the frontier is always a subset of the marked set.
Inv2 == frontier \subseteq marked

\* Invariant: the marked set is exactly the reachable set from the root.
Inv3 == marked = { y \in Nodes : \E s \in LimitedSeq(Nodes) :
                   /\ Len(s) > 0
                   /\ Head(s) = Root
                   /\ Last(s) = y
                   /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in ConnectedToSomeButNotAll[s[i]] } }

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ marked' = marked \cup ConnectedToSomeButNotAll[x]
       /\ frontier' = ConnectedToSomeButNotAll[x]
  /\ UNCHANGED pc

Finish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ Finish

\* Any node reachable from the root is eventually marked.
PartialCorrectness == \A y \in Nodes : (y \in marked) ~> (y \in marked)

Termination == <>(pc = "done")

Spec == Init /\ [][Next]_vars /\ Spec

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, so Succ is never
\* declared here and the inherited actions keep using Succ (now grounded).
ConnectedToSomeButNotAll(x) ==
  CASE x = 1 : {2, 3}
  []   x = 2 : {3, 4}
  []   x = 3 : {1, 4}
  []   x = 4 : {1, 2}

\* The .cfg substitutes LimitedSeq for Seq (bound to the number of nodes),
\* so while Sequences is still EXTENDED, the unbounded Seq name is never
\* used; the model is forced to use this bounded version instead.
LimitedSeq(A) == { s \in Seq(A) : Len(s) <= Cardinality(Nodes) }

====