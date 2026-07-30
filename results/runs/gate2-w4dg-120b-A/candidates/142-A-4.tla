---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "start"

StartStep ==
  /\ pc = "start"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Mark(v) ==
  /\ pc = "running"
  /\ v \in frontier
  /\ marked' = marked \cup {v}
  /\ frontier' = frontier \ {v}
  /\ frontier' = frontier' \cup Succ(v)
  /\ UNCHANGED pc

DoneStep ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ StartStep
  \/ \E v \in Nodes : Mark(v)
  \/ DoneStep

MarkStep == \E v \in Nodes : Mark(v)
RunningStep == MarkStep \/ DoneStep
Spec == Init /\ [][Next]_vars /\ WF_vars(RunningStep)

MarkedFrontier == marked \cup frontier
MarkedReach == ReachableFrom(Root, Nodes, marked)
FrontierReach == ReachableFrom(Root, Nodes, frontier)

CompleteMarking ==
  marked = ReachableFrom(Root, Nodes, Nodes)

Invariant1 ==
  /\ TypeOK
  /\ \A u \in marked : Succ(u) \subseteq MarkedFrontier

Invariant2 ==
  /\ ReachableFrom(Root, Nodes, MarkedFrontier) = MarkedReach
  /\ ReachableFrom(Root, Nodes, frontier) = FrontierReach

Invariant3 ==
  ReachableFrom(Root, Nodes, Nodes) = MarkedFrontier \cup FrontierReach

====