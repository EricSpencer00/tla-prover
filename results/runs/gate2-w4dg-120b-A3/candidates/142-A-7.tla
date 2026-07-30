---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup ReachableFrom(S \cup Succ(x))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore ==
  /\ pc = "idle"
  /\ \E n \in marked : frontier' = frontier \cup Succ(n)
  /\ pc' = "done"
  /\ UNCHANGED marked

MoveToMarked ==
  /\ pc = "done"
  /\ frontier # {}
  /\ \E n \in frontier : marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = "idle"

AllMarkned ==
  /\ frontier = {}
  /\ \A n \in Nodes : n \in marked
  /\ UNCHANGED vars

Next == Init \/ Explore \/ MoveToMarked \/ AllMarkned

Spec == Init /\ [][Next]_vars

InductiveType ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

AllInvariantsHold == InductiveType /\ Invariant2 /\ Invariant3

====