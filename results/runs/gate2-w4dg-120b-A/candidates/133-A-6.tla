---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ Len(frontier) <= Cardinality(Nodes)
  /\ pc \in [Procs -> {"idle", "seeing", "done", "done2"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> CHOOSE n \in Nodes : TRUE]
  /\ succs = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ frontier # <<>>
  /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "seeing"]
  /\ succs' = [succs EXCEPT ![p] = Succ[Head(frontier)]]
  /\ UNCHANGED marked

Mark(p) ==
  /\ pc[p] = "seeing"
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<frontier, sel, succs>>

Sprout(p) ==
  /\ pc[p] = "done"
  /\ marked' = marked \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "done2"]
  /\ UNCHANGED <<frontier, sel, succs>>

Recycle(p) ==
  /\ pc[p] = "done2"
  /\ Cardinality(marked) < Cardinality(Nodes)
  /\ frontier' = frontier \o <<sel[p]>>
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, sel>>

Next ==
  \E p \in Procs : Select(p) \/ Mark(p) \/ Sprout(p) \/ Recycle(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====