---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ pc = "idle"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Expand ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ UNCHANGED pc

Done ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Expand \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == \A n \in marked : \E m \in frontier : n \in Succ[m]
Inv2 == \A n \in Nodes : (n \in marked) <=> (\E m \in Nodes : n \in Succ[m])
Inv3 == \A n \in Nodes : (n \in frontier) => (n \in marked)
PartialCorrectness == \A n \in Nodes : n \in marked

Termination == <>(pc = "done")

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == [n \in 1..Cardinality(Nodes) |-> CHOOSE x \in Nodes : TRUE]

====