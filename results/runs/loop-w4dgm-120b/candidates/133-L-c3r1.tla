---- MODULE MCParReach ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succs = [n \in Nodes |-> Succ[n]]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "selected"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![n] = ConnectedToSomeButNotAll(n)]
  /\ UNCHANGED marked

Mark(p) ==
  /\ pc[p] = "selected"
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<frontier, selected, succs>>

Pass(p) ==
  /\ pc[p] = "selected"
  /\ selected[p] \in marked
  /\ frontier' = frontier \cup succs[selected[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, selected, succs>>

AllIdle == \A p \in Procs : pc[p] = "idle"

Quiesce ==
  /\ AllIdle
  /\ frontier = {}
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Pass(p)
  \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selected", "crashed"}]
  /\ selected \in [Procs -> Nodes]
  /\ succs \in [Nodes -> SUBSET Nodes]

ControlFlowOK ==
  /\ (\A p \in Procs : pc[p] = "selected" => selected[p] \in frontier)
  /\ (\A p \in Procs : pc[p] = "crashed" => selected[p] \in frontier)

Inv == TypeOK /\ ControlFlowOK

\* Refinement: the parallel algorithm never marks a node unless it was
\* reachable from the frontier, which is exactly what the sequential Misra
\* algorithm would also require of any such marking.
Refines == \A n \in marked \ {Root} : \E m \in Nodes : n \in succs[m]

\* The .cfg file substitutes ConnectedToSomeButNotAll for Succ and
\* LimitedSeq for Seq. Here Succ is a constant function; ConnectedToSomeButNotAll
\* is a finite override, and LimitedSeq would be the finite version of Seq.

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(s) == s

====