---- MODULE MCParReach ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"
MaxSeq == Cardinality(Nodes)

VARIABLES marked, frontier, pc, selected, succlist

vars == <<marked, frontier, pc, selected, succlist>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> NONE]
  /\ succlist = [p \in Procs |-> <<>>]

Take(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "taken"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ UNCHANGED <<marked, succlist>>

TakeAny(p) ==
  \E n \in Nodes : Take(p, n)

Mark(p) ==
  /\ pc[p] = "taken"
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ succlist' = [succlist EXCEPT ![p] = <<>>]
  /\ pc' = [pc EXCEPT ![p] = "marked"]
  /\ UNCHANGED <<frontier, selected>>

ReRead(p) ==
  /\ pc[p] = "taken"
  /\ selected[p] \in marked
  /\ succlist' = [succlist EXCEPT ![p] = <<>>]
  /\ pc' = [pc EXCEPT ![p] = "summing"]
  /\ UNCHANGED <<marked, frontier, selected>>

ReadSucc(p) ==
  /\ pc[p] \in {"marked", "summing"}
  /\ Len(succlist[p]) < MaxSeq
  /\ succlist' = [succlist EXCEPT ![p] = Append(@, selected[p])]
  /\ pc' = [pc EXCEPT ![p] = "summing"]
  /\ UNCHANGED <<marked, frontier, selected>>

AddSet(p) ==
  /\ pc[p] = "summing"
  /\ Len(succlist[p]) > 0
  /\ frontier' = frontier \cup Succ(Head(succlist[p]))
  /\ succlist' = [succlist EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<marked, pc, selected>>

IdleStep ==
  /\ \A p \in Procs : pc[p] = "idle"
  /\ \E n \in Nodes : TakeAny(Arbitrary(Procs), n)

Next ==
  \/ \E p \in Procs, n \in Nodes : Take(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : ReRead(p)
  \/ \E p \in Procs : ReadSucc(p)
  \/ \E p \in Procs : AddSet(p)
  \/ IdleStep

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] \in {"idle", "taken", "marked", "summing"}
  /\ \A p \in Procs : selected[p] \in Nodes \cup {NONE}
  /\ \A p \in Procs : succlist[p] \in Seq(Nodes)
  /\ \A x \in marked : \E p \in Procs : selected[p] = x

Refines ==
  /\ \A p \in Procs : pc[p] # "idle" => selected[p] \in frontier
  /\ \A p \in Procs : pc[p] = "summing" => Len(succlist[p]) > 0
  /\ \A p \in Procs : pc[p] = "summing" => \A i \in 1..Len(succlist[p]) : succlist[p][i] \in frontier

ConnectedToSomeButNotAll ==
  \E p \in Procs : \E i \in 1..Len(succlist[p]) : Succ(succlist[p][i])

LimitedSeq == Seq

====