---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup ReachFrom(S \ {x} \cup Succ(x))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "active"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ frontier # {}
  /\ LET x == CHOOSE y \in frontier : TRUE IN
       /\ marked' = marked \cup {x}
       /\ frontier' = (frontier \ {x}) \cup Succ(x)
  /\ pc' = IF frontier = {} THEN "idle" ELSE "active"

Next == Step

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 ==
  ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)

Invariant3 ==
  ReachFrom(Nodes) = marked \cup ReachFrom(frontier)

Theorem == (\A n \in Nodes : n \in ReachFrom({Root}) => n \in marked) /\ (frontier = {} => \A n \in Nodes : n \in ReachFrom({Root}) <=> n \in marked)

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {Theorem}
====