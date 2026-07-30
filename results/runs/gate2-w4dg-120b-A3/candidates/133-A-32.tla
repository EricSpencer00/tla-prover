---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ pc \in [Procs -> {"idle", "select", "explore", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ frontier # <<>>
  /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ UNCHANGED <<marked, succs>>

Explore(p) ==
  /\ pc[p] = "select"
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll(sel[p])]
  /\ marked' = marked \cup succs[p]
  /\ frontier' = Append(frontier, succs[p])
  /\ pc' = [pc EXCEPT ![p] = "explore"]
  /\ UNCHANGED <<sel>>

Finish(p) ==
  /\ pc[p] = "explore"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs: Select(p)
  \/ \E p \in Procs: Explore(p)
  \/ \E p \in Procs: Finish(p)
  \/ \E p \in Procs: Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

ConnectedToSomeButNotAll(n) ==
  ConnectedToSomeButNotAll

LimitedSeq(s) == LimitedSeq
====