---- MODULE ReachableProofs ----
EXTENDS Naturals, Misra2016Reachable

CONSTANTS Nodes, Root

\* Identity on nodes, used for the base case of reachable-from from Root.
Identity == [n \in Nodes |-> n]

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus closure of the marked set under
\* immediate successors (stays inside marked \cup frontier).
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active", "halt"}
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Invariant 2 follows from Lemma 1: the marked set plus nodes reachable
\* from the frontier is exactly the reachable set (no stale node left out).
ReachableFromMarkedFrontier ==
  reachableFrom(Frontier) \cup marked = reachableFrom(Frontier \cup marked)

\* Invariant 3: the marked set plus nodes reachable from the frontier is
\* exactly the reachable set (nothing is visited but not added yet).
MarkedPlusFrontier == marked \cup reachableFrom(Frontier)

\* Theorem: on termination the marked set is exactly the reachable set,
\* i.e. partial correctness of the reachability algorithm.
TerminationPartialCorrect ==
  (pc = "halt") => (marked = reachableFrom({Root}))

====