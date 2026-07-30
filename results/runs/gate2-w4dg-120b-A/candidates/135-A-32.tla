---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

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
  /\ pc = "running"

Expand(v) ==
  /\ frontier = {v}
  /\ pc = "running"
  /\ \E w \in Succ[v] : frontier' = {w}
  /\ marked' = marked \cup Succ[v]
  /\ UNCHANGED pc

Quiesce ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Expand(_)]_vars /\ [][Quiesce]_vars

Inv1 ==
  /\ marked \subseteq (UNION {Succ[v] : v \in Nodes})
  /\ marked \cup frontier = Nodes

Inv2 == frontier \subseteq (UNION {Succ[v] : v \in marked})

Inv3 == marked = Nodes

Termination == <>(pc = "done")

PartialCorrectness == \A w \in Nodes : (\E s \in Seq : s[1] = Root /\ Len(s) <= Cardinality(Nodes) /\ \A i \in 1..Len(s) : s[i] \in marked /\ s[i] \in Succ[s[i-1]]) => w \in marked

====