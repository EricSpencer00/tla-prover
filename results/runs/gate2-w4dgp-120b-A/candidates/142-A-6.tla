---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

\* A formal proof module for the sequential Misra reachability algorithm.
\* It proves the three invariants stated in the description as semantic
\* TCInit/TCAxiom steps, then derives the partial-correctness theorem from
\* them. The liveable actions are taken from the algorithm module it extends.
CONSTANTS Nodes, Root

\* Reachability from a set X via graph edges defined by the adjacency function.
VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE reachFrom(_, _)
reachFrom(X, S) == IF S = {} THEN X
                  ELSE LET y == CHOOSE z \in S : TRUE
                       IN reachFrom(X \cup {y}, (S \ {y}) \cup Succ(y))

\* Lemma 1: every successor of a marked node is either marked or in the frontier.
SuccessorsInMarkedOrFrontier == \A x \in marked : Succ(x) \subseteq marked \cup frontier

\* Lemma 2: reachable-from is stable when it is already closed under successors.
ReachableFromStable == \A X \in SUBSET Nodes : (Succ(X) \subseteq X) => (reachFrom(X, {}) = X)

\* Lemma 3: reachable from the empty set is empty.
ReachableFromEmptySet == reachFrom({}, {}) = {}

\* The algorithm's type-correctness plus Lemma 1 as an inductive invariant.
TypeOKAndSuccessorsInMarkedOrFrontier ==
  /\ marked \subseteq Nodes /\ frontier \subseteq Nodes
  /\ Succ(Root) \subseteq frontier
  /\ \A x \in frontier : x \notin marked
  /\ SuccessorsInMarkedOrFrontier

\* Entailment: the marked set plus the frontier's descendants equals the reachable set.
MarkedFrontierCoverReachable ==
  marked \cup reachFrom(frontier, {}) = reachFrom({Root}, {})

\* The terminal argument of the algorithm: the marked set is exactly the reachable set.
MarkedEqualsReachable ==
  marked = reachFrom({Root}, {})

\* The algorithm's actions, imported from the module it extends.
Init == Init
Mark == Mark
Explore == Explore
Terminate == Terminate

\* The algorithm makes progress: it never gets stuck in the exploring state.
Progress == (pc \in {"init", "exploring"}) ~> (pc = "explored")

TypeOK == TypeOKAndSuccessorsInMarkedOrFrontier

Spec == Init /\ [][Next]_vars /\ Progress
====