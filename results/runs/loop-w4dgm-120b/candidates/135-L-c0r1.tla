---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Mark(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ pc' = pc

Explore(n) ==
  /\ pc = "running"
  /\ n \in marked
  /\ n \notin frontier
  /\ frontier' = frontier \cup {n}
  /\ pc' = pc
  /\ marked' = marked

Complete ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes : Explore(n)
  \/ Complete
  \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in frontier : n \notin marked

Inv2 ==
  \A n \in marked : \E m \in frontier : n \in Succ[m]

Inv3 ==
  \A n \in Nodes : (n \in marked) <=> (\E m \in Nodes : n \in Succ[m])

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) => (\E m \in Nodes : n \in Succ[m])

Termination ==
  <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====