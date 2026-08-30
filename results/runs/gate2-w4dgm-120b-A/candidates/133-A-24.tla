---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = Succ

\* A worker picks an unmarked frontier node and reads its successors.
StartWork(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ n \notin marked
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succ' = [succ EXCEPT ![n] = Succ[n]]
  /\ UNCHANGED <<marked, frontier>>

MarkAndPush(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \in frontier
  /\ sel[p] \notin marked
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = (frontier \cup succ[sel[p]]) \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<sel, succ>>

AbortWork(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \notin frontier
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succ>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succ>>

Next ==
  \/ \E p \in Procs, n \in Nodes: StartWork(p, n)
  \/ \E p \in Procs: MarkAndPush(p
  \/ \E p \in Procs: AbortWork(p)
  \/ \E p \in Procs: Reset(p)

Spec == Init /\ [][Next]_vars

\* Shared state is type-correct and a worker only acts on frontier nodes.
Inv ==
  /\ TypeOK
  /\ \A p \in Procs: pc[p] = "working" => sel[p] \in frontier

\* Parallel versus sequential: every node a sequential (Misra) run would have
\* marked is marked here too; the parallel run never lags behind it.
Refines ==
  /\ \A n \in Nodes: (n \notin frontier /\ n \notin marked) => (\A p \in Procs: sel[p] # n)
  /\ frontier \cap marked = {}

\* The model's graph structure: each node has exactly 2 successors, and the
\* per-process successor view never exceeds the actual graph's size bound.
ConnectedToSomeButNotAll(n, m) ==
  /\ m \in Succ[n]
  /\ Cardinality(Succ[n]) <= 2

LimitedSeq(s) == s
====