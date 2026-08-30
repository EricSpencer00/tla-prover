---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Step(n) ==
  /\ n \in frontier
  /\ frontier' = (frontier \ {n}) \cup Succ[n]
  /\ marked' = marked \cup Succ[n]
  /\ UNCHANGED pc

Complete ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes: Step(n)
  \/ Complete

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A a \in Nodes, b \in Nodes: (a \in marked /\ b \in Succ[a]) => b \in marked

Inv2 ==
  \A n \in Nodes: (\E p \in LimitedSeq(Nodes): Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\ \A k \in 1..(Len(p) - 1): p[k+1] \in Succ[p[k]])

Inv3 ==
  \A n \in Nodes: n \in marked => \E p \in LimitedSeq(Nodes): Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\ \A k \in 1..(Len(p) - 1): p[k+1] \in Succ[p[k]]

PartialCorrectness ==
  \A n \in Nodes: (n \in marked <=> \E p \in LimitedSeq(Nodes): Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\ \A k \in 1..(Len(p) - 1): p[k+1] \in Succ[p[k]])

Termination ==
  [][pc = "running" |_> \E n \in Nodes: p \in Succ[n] /\ p \in marked]

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====