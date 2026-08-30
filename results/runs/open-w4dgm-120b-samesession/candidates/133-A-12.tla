---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

NONE == "none"
MaxV == Cardinality(Nodes)

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> 0]
  /\ selected = [p \in Procs |-> NONE]
  /\ succs = [n \in Nodes |-> Succ[n]]

Select(p, n) ==
  /\ pc[p] = 0
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ succs' = succs
  /\ marked' = marked

Mark(p) ==
  /\ pc[p] = 1
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = frontier \cup succs[selected[p]]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ selected' = [selected EXCEPT ![p] = NONE]
  /\ succs' = succs

Skip(p) ==
  /\ pc[p] = 1
  /\ selected[p] \in marked
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ selected' = [selected EXCEPT ![p] = NONE]
  /\ frontier' = frontier
  /\ succs' = succs
  /\ marked' = marked

Reset(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ selected' = selected
  /\ frontier' = frontier
  /\ succs' = succs
  /\ marked' = marked

Next ==
  \/ \E p \in Procs, n \in frontier : Select(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Skip(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] \in 0..2
  /\ \A p \in Procs : (pc[p] = 1) => (selected[p] \in frontier)
  /\ \A n \in frontier : n \notin marked
  /\ \A n \in Nodes : succs[n] \subseteq Nodes
  /\ \A n \in Nodes : n \notin marked => (Marked \cup {n}) \notin frontier

Refines == Inv

ConnectedToSomeButNotAll(n) == succs[n]

LimitedSeq(S) == {S[i] : i \in 1..Len(S)}

====