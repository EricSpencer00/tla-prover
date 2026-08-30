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
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Explore(p, m) ==
  /\ pc[p] = "selecting"
  /\ m \in ConnectedToSomeButNotAll(n, marked)
  /\ succs' = [succs EXCEPT ![p] = Append(succs[p], m)]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, sel>>

Commit(p) ==
  /\ pc[p] = "exploring"
  /\ marked' = marked \cup {succs[p][1]}
  /\ frontier' = frontier \cup {succs[p][1]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = << >>]

Abort(p) ==
  /\ pc[p] = "exploring"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, m \in Nodes : Explore(p, m)
  \/ \E p \in Procs : Commit(p)
  \/ \E p \in Procs : Abort(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

ConnectedToSomeButNotAll(n, S) ==
  {m \in Nodes : m \in Succ[n] /\ m \notin S}

LimitedSeq == Seq

====