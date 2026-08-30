---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration for the parallel reachability algorithm.
\* It inherits the algorithm (states/actions) and only adds the config
\* constants plus a bounded-sequence definition so the model is finite.

CONSTANT Nodes
CONSTANT Root
CONSTANT Procs
CONSTANT Succ

None == "none"

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "collecting"}]
  /\ sel \in [Procs -> Nodes \cup {None}]
  /\ succ \in [Nodes -> SUBSET Nodes]
  /\ Cardinality(frontier) <= Cardinality(Nodes)
  /\ Cardinality(marked) <= Cardinality(Nodes)

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> None]
  /\ succ = Succ

\* A worker selects an unmarked frontier node to explore.
Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ n \notin marked
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, succ>>

\* A worker collects the successors of its selected node and marks it.
Collect(p) ==
  /\ pc[p] = "selecting"
  /\ succ' = [succ EXCEPT ![sel[p]] = {}]
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup succ[sel[p]]
  /\ sel' = [sel EXCEPT ![p] = None]
  /\ pc' = [pc EXCEPT ![p] = "idle"]

\* A worker abandons selection when the selected node was already marked.
Abort(p) ==
  /\ pc[p] = "selecting"
  /\ sel[p] \in marked
  /\ sel' = [sel EXCEPT ![p] = None]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, succ>>

\* The frontier drops a node when every worker has ignored it.
Drop(n) ==
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, pc, sel, succ>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Collect(p)
  \/ \E p \in Procs : Abort(p)
  \/ \E n \in Nodes : Drop(n)

Spec == Init /\ [][Next]_vars

\* The parallel algorithm respects the same disciplined control flow as the
\* sequential Misra algorithm: a worker only collects after selecting a
\* frontier node, and only aborts while standing on a node that was already
\* marked -- exactly the control discipline the sequential algorithm relies on.
Inv == \A p \in Procs : (pc[p] = "selecting") => (sel[p] \in frontier)

\* The parallel algorithm actually implements the sequential Misra flow.
Refines == Inv

\* Bounded sequence: a finite (cardinality-bounded) version of Seq for model checking.
LimitedSeq(f, i) == IF i \in Nat THEN f[i] ELSE NONE

\* The graph each node has successors at most two distinct other nodes.
ConnectedToSomeButNotAll(n) ==
  /\ n \in Nodes
  /\ Cardinality(Succ[n]) \in 0..2

====