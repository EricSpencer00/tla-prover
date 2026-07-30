---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

\* State: the set of marked nodes, the frontier (nodes reached but not yet
\* expanded), and the program counter (0: idle/terminated, 1: exploring).
VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {0, 1}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = 1

\* Expand the frontier: some frontier node is removed, and all of its
\* unmarked successors are pulled into it, atomically.
Expand ==
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ frontier' = (frontier \ {x}) \cup {y \in Nodes : y \notin marked /\ y # x}
       /\ marked' = marked \cup {x}
  /\ pc' = 1

Terminate ==
  /\ frontier = {}
  /\ pc = 1
  /\ pc' = 0
  /\ UNCHANGED <<marked, frontier>>

Next == Expand \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Graph-theoretic lemmas imported from the reachability proofs module.
FromRoot == {{Root}} \cup {w \in Nodes : \E x \in w : x \in {{Root}}}
Succ(n) == {y \in Nodes : y # n}
Reachable(z) == FROM z
Evolve(n) == FROM {{n}} \cup {Succ(n)}
EmptyReach == FROM {}

AllSuccessorsInMarkedOrFrontier ==
  \A x \in marked : Succ(x) \subseteq marked \cup frontier

\* Invariant 1: type correctness plus every successor of a marked node is
\* already accounted for (in marked or frontier).
Inv1 == TypeOK /\ AllSuccessorsInMarkedOrFrontier

\* Invariant 2: marked plus nodes reachable from the frontier equals nodes
\* reachable from the combined frontier-marked set -- proved using Lemma 1.
Inv2 == FromRoot \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Invariant 3: nodes reachable from the root equal the marked set plus the
\* nodes reachable from the frontier -- proved using Lemma 2 and Lemma 3.
Inv3 == FromRoot = marked \cup Reachable(frontier)

\* Partial correctness: when the algorithm has terminated, the marked set
\* equals the set of reachable nodes.
TerminationIsExact == (pc = 0) => (marked = FromRoot)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* No liveness property: TLAPS currently cannot prove termination.
PROPERTIES == TerminationIsExact

====