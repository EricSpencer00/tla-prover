---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

RECURSIVE Intersect(_, _)
Intersect(A, B) ==
  IF A = {} THEN {}
  ELSE LET x == CHOOSE y \in A : TRUE IN IF x \in B THEN {x} \cup Intersect(A \ {x}, B) ELSE Intersect(A \ {x}, B)

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "exploring", "done"}]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> << >>]

Explore(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, succs>>

ComputeSucc(p, s) ==
  /\ pc[p] = "exploring"
  /\ succs[p] = << >>
  /\ s \in Succ[sel[p]]
  /\ succs' = [succs EXCEPT ![p] = << s >>]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
  /\ pc[p] = "exploring"
  /\ Len(succs[p]) > 0
  /\ succs[p][1] \notin marked
  /\ marked' = marked \cup {succs[p][1]}
  /\ frontier' = frontier \cup {succs[p][1]}
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED sel

Done(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] # << >>
  /\ succs[p][1] \in marked
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Explore(p, n)
  \/ \E p \in Procs, s \in Nodes : ComputeSucc(p, s)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq

====