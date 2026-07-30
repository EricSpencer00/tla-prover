---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "init"

Explore ==
  /\ pc = "init"
  /\ frontier' = {y \in Nodes : \E x \in marked : y \in Edges(x)}
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Mark ==
  /\ pc = "exploring"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "exploring"

DoneExploring ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Explore
  \/ Mark
  \/ DoneExploring
  \/ Done

InitInv ==
  /\ TypeOK
  /\ \A x \in marked : (\A y \in Edges(x) : y \in marked \cup frontier)

Inv2 ==
  marked \cup ReachableSet(frontier) = ReachableSet(marked \cup frontier)

Inv3 ==
  ReachableSet(Root) = marked \cup ReachableSet(frontier)

Spec == Init /\ [][Next]_vars

Invariants ==
  /\ InitInv
  /\ Inv2
  /\ Inv3

Properties ==
  /\ InitInv
  /\ Inv2
  /\ Inv3

====