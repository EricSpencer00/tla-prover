---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

ReachStep ==
  /\ frontier # {}
  /\ pc \in {"idle", "searching"}
  /\ \E n \in frontier:
       /\ marked' = marked \union {n}
       /\ frontier' = frontier \union Succ[n]
  /\ pc' = IF frontier' = Nodes THEN "done" ELSE "searching"

Terminate == /\ pc = "done" /\ UNCHANGED vars

Next == ReachStep \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq marked
Inv2 == \A e \in marked : \E s \in Seq : s # << >> /\ s[1] = Root /\ e \in SubsetSeq(s)
Inv3 == marked \subseteq {e \in Nodes : \E s \in Seq : s # << >> /\ s[1] = Root /\ e \in SubsetSeq(s)}
PartialCorrectness == \A e \in marked : (e \in Succ[Root] \/ \E n \in Nodes : e \in Succ[n])

SubsetSeq(s) == {s[i] : i \in DOMAIN s}

Termination == <>(pc = "done")

====