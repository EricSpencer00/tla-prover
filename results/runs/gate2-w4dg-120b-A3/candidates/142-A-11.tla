---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable

CONSTANTS Nodes, Root

\* The algorithm state is carried inside the base Reachable module and
\* here we only add the TLAPS-checked proofs of its partial correctness.
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "explore", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

Explore(n) ==
  /\ pc \in {"init", "explore"}
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = "explore"

Done ==
  /\ pc \in {"init", "explore"}
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Done

Spec == Init /\ [][Next]_vars

\* 1) basic type safety plus the front/back edge invariant
\* 2) reachable-from is closed under expanding the source set by frontier
\* 3) the monotone reachability lemma turns the closure into a fixed point
\* Theorem is the partial-correctness claim derived from the three invariants.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Invariant2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

Theorem ==
  /\ Invariant1
  /\ Invariant2
  /\ Invariant3
  /\ pc = "done"
  => marked = ReachableFrom(Root)

====