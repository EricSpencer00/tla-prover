---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachableAlg, ReachableLemmas

CONSTANTS Nodes, Root

RECURSIVE ReachableFrom(_, _)
ReachableFrom(S, V) == IF V = {} THEN {} ELSE
  LET x == CHOOSE y \in V : TRUE IN {x} \cup ReachableFrom(S, V \cup S[x])

InitState == InitReachable

NextStep == NextReachable

Spec == SpecReachable

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "collect", "done"}

\* Every successor of a marked node is already marked or in the frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : (Successors[n] \subseteq marked) \/ (Successors[n] \subseteq frontier)

\* The marked set plus nodes reachable from the frontier equals the nodes
\* reachable from the union of marked and frontier.
Invariant2 ==
  ReachableFrom(Successors, marked) = ReachableFrom(Successors, marked \cup frontier)

\* The reachable set equals the marked set plus nodes reachable from the frontier.
Invariant3 ==
  ReachableFrom(Successors, {Root}) = ReachableFrom(Successors, marked \cup frontier)

\* Partial correctness: when the algorithm is done, the marked set is exactly
\* the reachable set.
Correctness ==
  pc = "done" => marked = ReachableFrom(Successors, {Root})

====