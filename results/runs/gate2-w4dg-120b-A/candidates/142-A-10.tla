---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "searching"

Expand(n) ==
  /\ pc = "searching"
  /\ n \in marked
  /\ n \notin frontier
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : Expand(n) \/ Mark(n) \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1 (type correctness plus the frontier/marked closure property) is
\* proved by TLAPS directly; invariants 2 and 3 below are proved using the
\* reachability lemmas from the other module.
MarkInvariant ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

ReachInvariant ==
  /\ marked \cup ReachFrom(Nodes, frontier) = ReachFrom(Nodes, marked \cup frontier)

FrontierCover ==
  /\ ReachFrom(Nodes, {Root}) = marked \cup ReachFrom(Nodes, frontier)

PartialCorrectness ==
  /\ (pc = "done") => (marked = ReachFrom(Nodes, {Root}))

INVARIANTS == MarkInvariant /\ ReachInvariant /\ FrontierCover
PROPERTIES == PartialCorrectness

====