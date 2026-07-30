---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, ReachabilityAlgos, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET x == CHOOSE y \in S : TRUE
        l == ReachFrom(S \ {x})
    IN {x} \cup l \cup (l \cup {x}) \cap frontier \cup (\E y \in S : (y \in l \cup {x}) /\ (y \in marked) /\ (y, x) \in Edges)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

FrontierDisjoint == marked \cap frontier = {}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore ==
  /\ pc = "idle"
  /\ pc' = "exploring"
  /\ frontier' = {y \in Nodes : (Root, y) \in Edges}
  /\ UNCHANGED marked

MarkNode ==
  /\ pc = "exploring"
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ marked' = marked \cup {x}
       /\ frontier' = frontier \ {x}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Explore
  \/ MarkNode
  \/ Terminate
  \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A x \in marked : \E y \in frontier \cup marked : (x, y) \in Edges

Invariant2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Invariant3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness == (pc = "done") ~> (marked = ReachFrom({Root}))

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {PartialCorrectness}
====