---- MODULE ReachableProofs ----
EXTENDS MisraReaches, ReachesLemmas, Sequences, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "recur"

Recur ==
  /\ pc = "recur"
  /\ \E v \in frontier:
       marked' = marked \cup {v}
       frontier' = (frontier \ {v}) \cup (Succ(v) \ marked)
  /\ pc' = pc

Halt ==
  /\ pc = "recur"
  /\ frontier = {}
  /\ pc' = "halt"
  /\ UNCHANGED <<marked, frontier>>

StartNewRound ==
  /\ pc = "halt"
  /\ pc' = "recur"
  /\ UNCHANGED <<marked, frontier>>

Deplete ==
  /\ pc = "halt"
  /\ frontier = {}
  /\ UNCHANGED vars

Next == Recur \/ Halt \/ StartNewRound \/ Deplete

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"recur", "halt"}
  /\ \A v \in marked: Succ(v) \subseteq (marked \cup frontier)

Inv1 ==
  TypeOK
  /\ \A v \in marked: Succ(v) \subseteq (marked \cup frontier)

Inv2 ==
  marked \cup ReachesFrom(frontier) = ReachesFrom(marked \cup frontier)

Inv3 ==
  ReachesFrom(Nodes) = marked \cup ReachesFrom(frontier)

PartialCorrectness == pc = "halt" => marked = ReachesFrom(Nodes)

====