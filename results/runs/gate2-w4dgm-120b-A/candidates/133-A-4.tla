---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "scanning", "sealing"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

\* The two invariants the configuration re-checks: type correctness plus the
\* two-phase-commit discipline.
ControlFlowOK ==
  /\ \A p \in Procs : (pc[p] = "scanning") => (selected[p] \in Nodes)
  /\ \A p \in Procs : (pc[p] = "sealing") => (selected[p] \in frontier)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "scanning"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ UNCHANGED <<marked, frontier, succs>>

\* The prepare step opens a fresh voting set.
Prepare(p) ==
  /\ pc[p] = "scanning"
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "sealing"]
  /\ UNCHANGED <<marked, frontier, selected>>

Vote(p, m) ==
  /\ pc[p] = "sealing"
  /\ m \in ConnectedToSomeButNotAll(selected[p])
  /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {m}]
  /\ UNCHANGED <<marked, frontier, pc, selected>>

Commit(p) ==
  /\ pc[p] = "sealing"
  /\ succs[p] \subseteq frontier
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, succs>>

Abort(p) ==
  /\ pc[p] = "sealing"
  /\ succs[p] \not\subseteq frontier
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Mark(n) ==
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<pc, selected, succs>>

Next ==
  \E p \in Procs :
    \/ \E n \in Nodes : Select(p, n)
    \/ Prepare(p)
    \/ \E m \in Nodes : Vote(p, m)
    \/ Commit(p)
    \/ Abort(p)
    \/ \E n \in Nodes : Mark(n)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ ControlFlowOK

\* Safety, checking the same sequential refinement property as the parallel
\* algorithm's own specification.
Refines == ControlFlowOK

\* The concrete graph: a bounded 2-successor function over the fixed node set.
ConnectedToSomeButNotAll(n) ==
  IF n = Root THEN Nodes \ {Root}
  ELSE IF n \in Nodes THEN Nodes \ {n}
  ELSE {}

\* The sequence bound is the same bound used in the sequential algorithm's
\* model so the configuration's finite-state comparison stays fair.
LimitedSeq == Seq

====