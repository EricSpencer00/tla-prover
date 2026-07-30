---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN Reachable(x) \cup ReachableFrom(S \ {x})

Init ==
  /\ marked = {Root}
  /\ frontier = Reachable(Root)
  /\ pc = "NC"

Expand ==
  /\ pc = "NC"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ marked' = marked \cup {x}
       /\ frontier' = (frontier \ {x}) \cup Reachable(x)
  /\ pc' = "NC"

Terminate ==
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Idle ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Expand
  \/ Terminate
  \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"NC", "Done"}

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Reachable(n) \subseteq marked \cup frontier

Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Invariant3 ==
  ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

NoDeadlock == TRUE

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PROPERTIES == Spec /\ NoDeadlock
====