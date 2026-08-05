---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, Reachable

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "exploring"

Mark ==
  /\ pc = "exploring"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
  /\ pc' = pc

Done ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next_ == Mark \/ Done

Inv1 == \A n \in frontier : n \in Nodes \ marked

Inv2 == \A n \in marked : \E p \in Seq(Nodes) : Len(p) > 0 /\ Head(p) = n /\ \A i \in 1 .. (Len(p) - 1) : p[i] \in Nodes /\ p[i + 1] \in Succ[p[i]]

Inv3 == \A n \in Nodes : n \in marked <=> \E p \in Seq(Nodes) : Len(p) > 0 /\ Head(p) = n /\ \A i \in 1 .. (Len(p) - 1) : p[i] \in Nodes /\ p[i + 1] \in Succ[p[i]]

PartialCorrectness == \A n \in Nodes : n \in marked => (n = Root) \/ \E y \in frontier : n \in Succ[y]

Spec == Init /\ [][Next_]_vars

ConnectedToSomeButNotAll == Succ

Termination == <>(pc = "done")

====