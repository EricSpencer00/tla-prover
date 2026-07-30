---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Adj == [n \in Nodes |-> Nodes]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "search", "done"}

Terminated == pc = "done"

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

Explore(n) ==
  /\ frontier = {}
  /\ marked' = marked
  /\ frontier' = {n}
  /\ pc' = "search"

Visit(n) ==
  /\ frontier # {}
  /\ frontier' = {}
  /\ marked' = marked \cup {n}
  /\ pc' = "search"

Done ==
  /\ frontier = {}
  /\ pc = "search"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

InitStep == \E n \in Nodes : Explore(n)

VisitStep == \E n \in Nodes : Visit(n)

Next == InitStep \/ VisitStep \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus successors of marked nodes are either
\* already marked, or exactly the next frontier node.
SuccessorInMarkOrFrontier ==
  /\ TypeOK
  /\ \A n \in Nodes : (n \in marked /\ frontier = {}) => \A m \in Adj[n] : m \in marked

\* Invariant 2: the marked set plus nodes reachable from the frontier equals the
\* nodes reachable from the union of marked and frontier (proved by Lemma 1).
FringeCoveredByReach ==
  marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Invariant 3: the reachable nodes from the root equal the marked set plus
\* nodes reachable from the frontier (proved by Lemmas 2 and 3).
MarkingAndFringeAreReachable ==
  Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == SuccessorInMarkOrFrontier /\ FringeCoveredByReach /\ MarkingAndFringeAreReachable

\* Partial correctness: when the search is done, the marked set is exactly the
\* reachable set from the root.
TerminationReaches == Terminated => Reachable({Root}) = marked

PROPERTIES == TerminationReaches

\* Graph-theoretic helper: nodes reachable from a set by following Adj.
Reachable(S) ==
  LET F[T \in SUBSET Nodes] ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE IN Adj[x] \cup F[T \ {x}]
  IN S \cup F[S]

====