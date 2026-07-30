---- MODULE MCReachable ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "running", "done"}

MarkedClosed ==
  \A n \in marked : \E m \in frontier : n \in Succ[m]

ReachableDecompose ==
  \A x \in Nodes : (x \in marked) <=> (\E s \in Seq : s[1] = Root /\ s[Len(s)] = x)

ReachableSetEqual ==
  \A n \in Nodes : (n \in frontier) => n \in marked

PartialCorrectness ==
  \A n \in marked : n \in frontier

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "init"

StepInit ==
  /\ pc = "init"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

MarkStep ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E m \in frontier :
       /\ marked' = marked \cup Succ[m]
       /\ frontier' = (frontier \cup Succ[m]) \ {m}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == StepInit \/ MarkStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

====