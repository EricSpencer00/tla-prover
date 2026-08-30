---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ succs' = [succs EXCEPT ![p] = Succ[sel[p]]]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p, i) ==
  /\ pc[p] = "working"
  /\ i \in DOMAIN succs[p]
  /\ succs[p][i] \notin marked
  /\ marked' = marked \cup {succs[p][i]}
  /\ frontier' = frontier \cup {succs[p][i]}
  /\ succs' = [succs EXCEPT ![p] = SubSeq(succs[p], 1, i - 1) \o SubSeq(succs[p], i + 1, Len(succs[p]))]
  /\ UNCHANGED <<pc, sel>>

Finish(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs, i \in 1..Len(succs[p]) : Mark(p, i)
  \/ \E p \in Procs : Finish(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

ConnectedToSomeButAll == Succ

LimitedSeq == Seq

====