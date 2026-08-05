---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succ

vars == <<marked, frontier, pc, selected, succ>>

MaxLen == Cardinality(Nodes)

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> 0]
  /\ succ = [n \in Nodes |-> Succ[n]]

Take(p) ==
  /\ pc[p] = "idle"
  /\ frontier # <<>>
  /\ selected' = [selected EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, succ>>

Mark(p) ==
  /\ pc[p] = "working"
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<frontier, selected, succ>>

Propagate(p) ==
  /\ pc[p] = "idle"
  /\ selected[p] \in marked
  /\ Len(frontier) < MaxLen
  /\ frontier' = Append(frontier, succ[selected[p]])
  /\ UNCHANGED <<marked, pc, selected, succ>>

Next ==
  \/ \E p \in Procs : Take(p)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Propagate(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ selected \in [Procs -> Nodes]
  /\ succ \in [Nodes -> SUBSET Nodes]

Refines == \A n \in Nodes : n \in marked

LimitedSeq == Seq(Nodes)

====