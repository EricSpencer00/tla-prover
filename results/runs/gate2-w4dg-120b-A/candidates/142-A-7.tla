---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableDefs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN ReachableFrom(S \ {x}) \cup Succ(x)
    {x} \cup Succ(x)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "init"

Explore ==
  /\ pc \in {"init", "running"}
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ frontier' = (frontier \ {n}) \cup Succ(n)
        /\ marked' = marked \cup {n}
  /\ pc' = "running"

Quit ==
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == Explore \/ Quit

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Invariant1 ==
  /\ TypeOK
  /\ \A x \in marked : Succ(x) \subseteq (marked \cup frontier)

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (ReachableFrom(Root) = marked)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====