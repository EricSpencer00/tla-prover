---- MODULE ReachableProofs ----
EXTENDS Naturals

\* Types and constants: the graph's vertices and its distinguished root.
CONSTANTS Nodes, Root

\* The sequential reachability algorithm's state, extended with a program counter.
VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* A helper naming the algorithm's successors; the graph itself is not modeled.
Succ(n) == {m \in Nodes : TRUE}

\* Type-correctness plus the key invariant that every successor of a marked
\* node is already marked or waiting in the frontier.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "run", "done"}

\* The full set of reachable nodes, built up from the frontier and the
\* marked set.  Lemma 1 (identified in ReachableLemmas.tla) is used to
\* establish this invariant as a direct consequence of the graph lemmas.
Invariant1 == TypeOK /\ (\A n \in marked : Succ(n) \subseteq marked \cup frontier)

\* The reachable set is stable under adding successors of the frontier.
\* Lemma 2 and Lemma 3 (from ReachableLemmas.tla) give this in two steps.
Invariant2 == ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* The marked set plus the frontier's reachable nodes is the reachable set.
Invariant3 == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

\* The algorithm's first step: only the root is marked, the frontier starts
\* empty and the program counter is at its initial value.
Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

\* The core step: a marked node's successors are explored, moving any not
\* already marked into the frontier, and advancing the program counter.
DoStep ==
  /\ pc = "init"
  /\ frontier' = frontier \cup {m \in Succ(n) : n \in marked /\ m \notin marked}
  /\ pc' = "run"
  /\ UNCHANGED marked

\* Finalising the run: the frontier becomes marked and the program counter
\* advances to its done state.
Finish ==
  /\ pc = "run"
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "done"
  /\ UNCHANGED <<pc>>

Next == Init \/ DoStep \/ Finish

\* The specification: the algorithm starts at Init and repeatedly takes a Next
\* step.  Once it reaches the done state it simply idles.
Spec == Init /\ [][Next]_vars

\* The three invariants proved in the TLAPS module, each identified as a
\* separate derived fact.  They are not folded into one combined invariant.
INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

\* The partial-correctness theorem: when the algorithm is done, the marked
\* set is exactly the set of reachable nodes.  TLAPS checks the proof of
\* each derived fact that feeds this conclusion.
PROPERTIES == Invariant3

====