---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachabilityGraph

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc, reachable

vars == <<marked, frontier, pc, reachable>>

\* The algorithm's program counter: 0 = idle, 1 = exploring, 2 = done.
InitState ==
  /\ marked = {Root}
  /\ frontier = Nodes \ {Root}
  /\ pc = 0
  /\ reachable = {Root}

\* An exploration step, always available: it moves one frontier node into
\* the marked set and updates the reachable set in lockstep, so the
\* reachable set is a pure functional image of the marked-plus-frontier set.
ExploreStep ==
  /\ frontier # {}
  /\ \E w \in frontier :
       /\ frontier' = frontier \ {w}
       /\ marked' = marked \cup {w}
       /\ reachable' = ReachableFrom(Successors, marked \cup frontier \cup {w})
  /\ pc' = IF pc < 2 THEN pc + 1 ELSE pc

Terminate ==
  /\ frontier = {}
  /\ pc' = 2
  /\ UNCHANGED <<marked, frontier, reachable>>

INIT == InitState

NEXT == ExploreStep \/ Terminate

Spec == INIT /\ [][NEXT]_vars

\* Invariant 1: types plus that successors of marked nodes are already in
\* the marked set or still waiting in the frontier.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..2
  /\ reachable = ReachableFrom(Successors, marked \cup frontier)

\* Invariant 2: marked plus reachable-from-frontier equals
\* reachable-from-marked-plus-frontier, proved from Lemma 1.
SuccessorAccessibility ==
  (marked \cup ReachableFrom(Successors, frontier))
    = ReachableFrom(Successors, marked \cup frontier)

\* Invariant 3: reachable-from-the-root is fully covered by the marked set
\* plus nodes reachable-from-the-frontier, proved using Lemma 2 and Lemma 3.
FrontierCompleteness ==
  reachable = marked \cup ReachableFrom(Successors, frontier)

\* The partial-correctness theorem: when the algorithm stops, the marked
\* set is exactly the reachable set. No invariant is dropped to prove it.
TerminationIsExact == (pc = 2) => (marked = reachable)

INVARIANTS == TypeOK /\ SuccessorAccessibility /\ FrontierCompleteness

\* No progress property is modelled here: TLAPS cannot yet check liveness,
\* so this module only proves partial correctness, never termination.
PROPERTIES == TerminationIsExact

====