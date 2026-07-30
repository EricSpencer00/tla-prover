---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes
CONSTANT Root
CONSTANT Procs
CONSTANT Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ selected \in [Procs -> Nodes \cup {0}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ selected = [p \in Procs |-> 0]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = 0
  /\ n \in frontier
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<marked, frontier, succs>>

Explore(p, n) ==
  /\ pc[p] = 1
  /\ n \in Succ(selected[p])
  /\ succs' = [succs EXCEPT ![p] = Append(succs[p], n)]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, selected>>

Mark(p) ==
  /\ pc[p] = 2
  /\ succs[p] # << >>
  /\ Head(succs[p]) \notin marked
  /\ marked' = marked \cup {Head(succs[p])}
  /\ frontier' = frontier \cup {Head(succs[p])}
  /\ UNCHANGED <<pc, selected, succs>>

ReplaceFrontier(p) ==
  /\ pc[p] \in {1, 2}
  /\ selected[p] \in frontier
  /\ frontier' = (frontier \ {selected[p]}) \cup {n \in Nodes : n \in Succ(selected[p])}
  /\ UNCHANGED <<marked, pc, selected, succs>>

Reset(p) ==
  /\ pc[p] \in {1, 2}
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ selected' = [selected EXCEPT ![p] = 0]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier>>

Quiesce ==
  /\ frontier = {}
  /\ \A p \in Procs : pc[p] = 0
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, n \in Nodes : Explore(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : ReplaceFrontier(p)
  \/ \E p \in Procs : Reset(p)
  \/ Quiesce

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in 0..2
  /\ \A p \in Procs : selected[p] \in Nodes \cup {0}
  /\ \A p \in Procs : Len(succs[p]) <= Cardinality(Nodes)

Refines == \A n \in Nodes : n \in marked

ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====