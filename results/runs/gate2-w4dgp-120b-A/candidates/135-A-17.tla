---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

NextOf == UNION {Succ[n] : n \in Nodes}
AllNodes == UNION {Succ[n] : n \in Nodes} \cup Nodes

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Inv1 == frontier \subseteq NextOf

Inv2 ==
  frontier = {n \in Nodes : Cardinality({s \in frontier : n \in Succ[s]}) > 0}

Inv3 == marked = {n \in Nodes : n \in frontier \/ Cardinality({s \in Nodes : n \in Succ[s]}) > 0}

PartialCorrectness == frontier \subseteq marked

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

SearchStep ==
  /\ pc = "idle"
  /\ pc' = "searching"
  /\ UNCHANGED <<marked, frontier>>

Explore(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ frontier' = frontier \cup Succ[n]
  /\ UNCHANGED <<marked, pc>>

Mark(n) ==
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ UNCHANGED <<frontier, pc>>

Complete ==
  /\ pc = "searching"
  /\ frontier \subseteq marked
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == SearchStep \/ Complete \/ (\E n \in Nodes : Explore(n)) \/ (\E n \in Nodes : Mark(n))

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

LimitedSeq == [n \in {0, 1, 2, 3} -> Nodes]

====