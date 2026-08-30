---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, chosen, succset

vars == <<marked, frontier, pc, chosen, succset>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..3]
  /\ chosen \in [Procs -> Nodes \cup {Root}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [q \in Procs |-> 0]
  /\ chosen = [q \in Procs |-> Root]
  /\ succset = [q \in Procs |-> {}]

Pick(q, n) ==
  /\ pc[q] = 0
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ chosen' = [chosen EXCEPT ![q] = n]
  /\ succset' = [succset EXCEPT ![q] = ConnectedToSomeButNotAll(n)]
  /\ pc' = [pc EXCEPT ![q] = 1]
  /\ UNCHANGED marked

Mark(q) ==
  /\ pc[q] = 1
  /\ marked' = marked \cup {chosen[q]}
  /\ pc' = [pc EXCEPT ![q] = 2]
  /\ UNCHANGED <<frontier, chosen, succset>>

Expand(q) ==
  /\ pc[q] = 2
  /\ frontier' = frontier \cup succset[q]
  /\ succset' = [succset EXCEPT ![q] = {}]
  /\ pc' = [pc EXCEPT ![q] = 0]
  /\ UNCHANGED <<marked, chosen>>

Next ==
  \/ \E q \in Procs, n \in Nodes: Pick(q, n)
  \/ \E q \in Procs: Mark(q)
  \/ \E q \in Procs: Expand(q)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \cap frontier = {}
  /\ \A q \in Procs: chosen[q] \in Nodes
  /\ \A q \in Procs: pc[q] \in 0..3
  /\ \A q \in Procs: (pc[q] = 2) => (succset[q] = {})
  /\ \A q \in Procs: (pc[q] = 1) => (chosen[q] \in Nodes)

Refines ==
  \A q \in Procs: (pc[q] = 3) ~> (pc[q] = 0)

ConnectedToSomeButNotAll(n) ==
  succset[n]

LimitedSeq(s) == s

====