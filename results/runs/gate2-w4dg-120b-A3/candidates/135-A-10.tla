---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Inv1 ==
  /\ frontier \subseteq marked
  /\ \A u \in frontier : \A v \in Succ[u] : v \in marked

Inv2 ==
  /\ marked \subseteq {Root} \cup (UNION {Succ[u] : u \in Nodes})

Inv3 ==
  /\ \A v \in Nodes : v \in marked => \E s \in LET S == UNION {Succ[u] : u \in Nodes} IN S : s = v

PartialCorrectness ==
  /\ \A u \in Nodes : u \in frontier => \E s \in Seq(Nodes) :
       /\ Len(s) <= Cardinality(Nodes)
       /\ s[1] = Root
       /\ s[Len(s)] = u
       /\ \A i \in 1..(Len(s) - 1) : s[i + 1] \in Succ[s[i]]

Expand(u) ==
  /\ pc = "running"
  /\ u \in frontier
  /\ frontier' = (frontier \ {u}) \cup (Succ[u] \ marked)
  /\ marked' = marked \cup Succ[u]
  /\ pc' = IF frontier = {u} THEN "done" ELSE pc

Next == \E u \in Nodes : Expand(u)

Spec == Init /\ [][Next]_vars

LimitedSeq ==
  LET S == UNION {Succ[u] : u \in Nodes} IN S

ConnectedToSomeButNotAll == Succ

Termination == <>(pc = "done")

====