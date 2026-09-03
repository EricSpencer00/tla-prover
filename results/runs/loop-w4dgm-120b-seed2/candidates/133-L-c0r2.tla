---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "selecting"
  /\ succs' = [succs EXCEPT ![p] = Succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, sel>>

Mark(p, m) ==
  /\ pc[p] = "exploring"
  /\ m \in succs[p]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = frontier \cup {m}
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {m}]
  /\ UNCHANGED <<pc, sel>>

Drop(p, m) ==
  /\ pc[p] = "exploring"
  /\ m \in succs[p]
  /\ m \in marked
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {m}]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Finish(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs, m \in Nodes : Mark(p, m)
  \/ \E p \in Procs, m \in Nodes : Drop(p, m)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "selecting", "exploring"}
  /\ \A p \in Procs : pc[p] = "idle" => sel[p] = "none"
  /\ \A p \in Procs : pc[p] = "selecting" => sel[p] \in Nodes
  /\ \A p \in Procs : pc[p] = "exploring" => succs[p] \subseteq Nodes

Refines ==
  /\ \A p \in Procs : pc[p] = "idle" => sel[p] = "none"
  /\ \A p \in Procs : pc[p] = "selecting" => sel[p] \in frontier
  /\ \A p \in Procs : pc[p] = "exploring" => succs[p] \subseteq Succ[sel[p]]

ConnectedToSomeButNotAll(n) == Cardinality(Succ[n]) > 0

LimitedSeq == Seq

====