---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE e \in S : TRUE IN Succ[x] \cup ReachFrom(S \ {x})

Inv1 == \A v \in marked : Succ[v] \subseteq (marked \cup frontier)

Inv2 == ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

Inv3 == ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness == ReachFrom({Root}) = marked

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(t) ==
  /\ pc = "running"
  /\ t \in frontier
  /\ \/ (t \notin marked /\ marked' = marked \cup {t} /\ frontier' = frontier \cup Succ[t])
     \/ (t \in marked /\ frontier' = frontier \ {t})
  /\ UNCHANGED pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E t \in Nodes : Explore(t) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

Termination == (pc = "running") ~> (pc = "done")

ConnectedToSomeButNotAll(v) == Succ[v]
LimitedSeq(n) == IF n <= 2 THEN n ELSE 2

====