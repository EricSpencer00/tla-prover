---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableSet(_)
ReachableSet(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN (ReachableSet(S \ {x}) \cup {x}) \cup (ReachableSet(ReachableOut(x)))

ReachableFromRoot == ReachableSet({Root})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running"}

Init ==
  /\ marked = {Root}
  /\ frontier = ReachableOut(Root)
  /\ pc = "running"

Next ==
  \/ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (ReachableOut(n))
        /\ UNCHANGED pc
  \/ \E n \in frontier :
        /\ frontier' = frontier \ {n}
        /\ UNCHANGED <<marked, pc>>
  \/ /\ pc = "running"
     /\ frontier = {}
     /\ pc' = "idle"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "idle"
     /\ marked = ReachableFromRoot
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : \A m \in ReachableOut(n) : m \in marked \cup frontier

Invariant2 ==
  ReachableSet(marked) \cup ReachableSet(frontier) = ReachableSet(marked \cup frontier)

Invariant3 ==
  ReachableFromRoot = marked \cup ReachableSet(frontier)

ReachableCorrectness == pc = "idle" => marked = ReachableFromRoot

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {ReachableCorrectness}
====