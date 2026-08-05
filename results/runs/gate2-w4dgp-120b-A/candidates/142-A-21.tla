---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachability, ReachableAlg

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = 0

ExploreStep(r, c) ==
  /\ pc = 0
  /\ r \in marked
  /\ c \in Succ[r]
  /\ c \notin marked
  /\ \A x \in frontier : c # x
  /\ frontier' = frontier \cup {c}
  /\ pc' = 1
  /\ UNCHANGED marked

MarkStep(c) ==
  /\ pc = 1
  /\ c \in frontier
  /\ marked' = marked \cup {c}
  /\ frontier' = frontier \ {c}
  /\ pc' = 0

ExploreAny ==
  \E r, c \in Nodes : ExploreStep(r, c)

MarkAny ==
  \E c \in Nodes : MarkStep(c)

Next ==
  \/ ExploreAny
  \/ MarkAny

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(ExploreAny)
  /\ SF_vars(MarkAny)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in 0..1
  /\ \A r \in marked : Succ[r] \subseteq (marked \cup frontier)

MarkClosure ==
  \A r \in marked : Succ[r] \subseteq (marked \cup frontier)

LinkFrontier ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

LinkReach ==
  Reachable(Root) = marked \cup ReachFrom(frontier)

CompleteCorollary == pc = 0 /\ frontier = {} => Reachable(Root) = marked

====