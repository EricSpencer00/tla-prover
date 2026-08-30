---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachableAlgs, GraphLemma, FiniteSets

CONSTANTS Nodes, Root

\* Re-proves the only three invariants in the line that follows.
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"idle", "search"}

Init ==
  /\ Marked = {Root}
  /\ Frontier = {}
  /\ pc = "idle"

Relax(n) ==
  /\ pc = "idle"
  /\ n \in Marked
  /\ n \notin Frontier
  /\ Frontier' = Frontier \cup {n}
  /\ pc' = "search"
  /\ UNCHANGED Marked

Commit(n) ==
  /\ pc = "search"
  /\ n \in Frontier
  /\ Frontier' = Frontier \ {n}
  /\ Marked' = Marked \cup Succ[n]
  /\ pc' = "idle"

Abandon(n) ==
  /\ pc = "search"
  /\ n \in Frontier
  /\ n \in Marked
  /\ Frontier' = Frontier \ {n}
  /\ pc' = "idle"

Idle ==
  /\ pc = "idle"
  /\ Frontier = {}
  /\ \A n \in Nodes : n \in Marked => Succ[n] \subseteq Marked
  /\ UNCHANGED <<Marked, Frontier, pc>>

Next ==
  \/ \E n \in Nodes : Relax(n) \/ Commit(n) \/ Abandon(n)
  \/ Idle

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* Invariant 1: inductive type plus every successor of a marked node is
\* already accounted for in the marked set or the frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in Marked : Succ[n] \subseteq (Marked \cup Frontier)

\* Invariant 2: the marked set plus the closure of the frontier already covers
\* the whole reachable set -- this is Lemma 1 from GraphLemma.
Invariant2 ==
  Marked \cup ReachableFrom(Frontier) = ReachableFrom(Marked \cup Frontier)

\* Invariant 3: the reachable set from the root is exactly the marked set plus
\* the closure of the frontier -- Lemma 2 plus Lemma 3 from GraphLemma.
Invariant3 ==
  ReachableFrom({Root}) = Marked \cup ReachableFrom(Frontier)

\* The reachable set collapses to the marked set at termination: partial
\* correctness of the sequential reachability algorithm.
TerminationIsComplete ==
  (Frontier = {}) => (ReachableFrom({Root}) = Marked)

INVARIANT TypeOK /\ Invariant1 /\ Invariant2 /\ Invariant3
PROPERTY TerminationIsComplete
====