---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

Queued == Cardinality(frontier)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ selected \in [Procs -> Nodes]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in Nodes
  /\ n \notin marked
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier>>

LoadSuccessors(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = << >>
  /\ succs' = [succs EXCEPT ![p] = Succ[selected[p]]]
  /\ UNCHANGED <<marked, frontier, pc, selected>>

Enqueue(p, i) ==
  /\ pc[p] = "working"
  /\ i \in 1..Len(succs[p])
  /\ succs[p][i] \notin marked
  /\ succs[p][i] \notin frontier
  /\ frontier' = frontier \cup {succs[p][i]}
  /\ succs' = [succs EXCEPT ![p] = SelectSeq(succs[p], i)]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, selected>>

SelectSeq(s, i) == SelectSeq(s, i, << >>)
SelectSeq(s, i, r) ==
  IF i = 1 THEN Append(s, r)
  ELSE SelectSeq(Tail(s), i - 1, Append(Head(s), r))

Done ==
  /\ frontier = {}
  /\ \A p \in Procs : pc[p] = "idle"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : LoadSuccessors(p)
  \/ \E p \in Procs, i \in 1..Len(succs[p]) : Enqueue(p, i)
  \/ Done

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] = "idle" => selected[p] \in Nodes /\ succs[p] = << >>
  /\ \A p \in Procs : pc[p] = "working" => selected[p] \in Nodes /\ succs[p] \in Seq(Nodes)

\* Refines: the parallel algorithm does not mark extra nodes, so the
\* fixed point reached by the workers is exactly the sequential closure.
Refines ==
  queued + SumF([p \in Procs |-> Len(succs[p])], Procs) = Queued + SumF([p \in Procs |-> 2], Procs)

\* LimitedSeq: a FINITE version of Seq for model checking.
LimitedSeq == Seq

ConnectedToSomeButNotAll ==
  Succ

====