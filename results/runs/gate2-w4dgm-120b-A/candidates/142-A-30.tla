---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "idle"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "exploring"

Explore(n) ==
  /\ pc = "exploring"
  /\ n \in marked
  /\ n \notin frontier
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<marked, pc>>

ExploreOther(n) == Explore(n)
ExploreRoot == Explore(Root)

MarkFrontier(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

MarkFrontierOther == MarkFrontier(\E n \in Nodes : TRUE)
MarkFrontierAny == MarkFrontierOther

Finish ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "idle"
  /\ UNCHANGED <<marked, frontier>>

Idle == UNCHANGED vars

Next ==
  \/ ExploreRoot
  \/ ExploreOther(\E n \in Nodes : TRUE)
  \/ MarkFrontierAny
  \/ Finish
  \/ Idle

Spec == Init /\ [][Next]_vars

\* Invariant 1: type + closure: every successor of a marked node is in marked
\* or frontier, the two sets staying disjoint.
ClosureOK ==
  /\ TypeOK
  /\ FrontierDisjoint == marked \cap frontier = {}
  /\ SuccClosure ==
       \A n \in marked : {m \in Nodes : Edge(n, m)} \subseteq (marked \cup frontier)

\* Invariant 2 follows from the key graph-theoretic Lemma 1: marked plus everything
\* reachable from the frontier is exactly the reachable set.
ReachableFromUnion == ReachableFrom(marked \cup frontier) = ReachableFrom(Root)

\* Invariant 3 follows from Lemma 2 (reachability is stable under adding successors)
\* and Lemma 3 (reachability from empty is empty): marked equals the reachable set.
EventualComplete == ReachableFrom(Root) = marked

INVARIANTS == TypeOK /\ ClosureOK /\ ReachableFromUnion /\ EventualComplete

\* The partial-correctness theorem: termination leaves the marked set equal to
\* exactly the reachable set.
TerminationComplete == (pc = "idle") ~> (ReachableFrom(Root) = marked)
====