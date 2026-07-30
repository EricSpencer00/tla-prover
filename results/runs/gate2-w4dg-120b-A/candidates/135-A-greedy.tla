---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

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

Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ marked' = marked \cup Succ[n]
  /\ UNCHANGED pc

Finish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Step
  \/ \E n \in Nodes : Explore(n)
  \/ Finish

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in frontier : \E m \in marked : n \in Succ[m]

Inv2 ==
  \A n \in marked : n # Root => \E m \in marked : n \in Succ[m]

Inv3 ==
  \A n \in Nodes : n \in marked => \E s \in Seq : s[1] = Root /\ s[Len(s)] = n

PartialCorrectness ==
  \A n \in Nodes : n \in marked => \E s \in Seq : s[1] = Root /\ s[Len(s)] = n

Termination == <>(pc = "done")

====