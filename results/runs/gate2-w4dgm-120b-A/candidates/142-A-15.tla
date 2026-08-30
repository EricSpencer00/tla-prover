---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachableSeq, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {}
  /\ pc = "idle"

MarkRoot ==
  /\ pc = "idle"
  /\ Root \notin marked
  /\ marked' = {Root}
  /\ frontier' = {}
  /\ pc' = "active"

AdvanceFrontier(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ(n)) \ marked
  /\ pc' = pc

DropFrontier(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = pc
  /\ marked' = marked

Terminate ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ marked' = marked
  /\ frontier' = frontier

Idle ==
  /\ pc = "done"
  /\ pc' = pc
  /\ marked' = marked
  /\ frontier' = frontier

Next ==
  \/ MarkRoot
  \/ \E n \in Nodes: AdvanceFrontier(n)
  \/ \E n \in Nodes: DropFrontier(n)
  \/ Terminate
  \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active", "done"}
  /\ (frontier \cap marked = {})
  /\ (FrontierIsBoundary == frontier \subseteq Succ(marked))

Invariant1 == TypeOK /\ FrontierIsBoundary
Invariant2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)
Invariant3 == ReachableFrom(Root) = (marked \cup ReachableFrom(frontier))
TerminationSaysReachable == (pc = "done") => (marked = ReachableFrom(Root))

Properties == Invariant1 /\ Invariant2 /\ Invariant3 /\ TerminationSaysReachable
====