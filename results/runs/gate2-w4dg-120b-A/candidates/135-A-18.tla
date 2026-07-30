---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "init"

Step ==
  /\ pc # "done"
  /\ \E n \in frontier :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = IF frontier = {} THEN "done" ELSE "searching"

Spec == Init /\ [][Step]_vars

Inv1 ==
  /\ frontier \subseteq (UNION {Succ[n] : n \in marked})
  /\ frontier \cap marked = {}

Inv2 ==
  \A n \in Nodes : n \in reachable(Root) => n \in marked

Inv3 ==
  \A n \in marked : n \in reachable(Root)

PartialCorrectness ==
  \A n \in reachable(Root) : n \in marked

Termination == <>(pc = "done")

====