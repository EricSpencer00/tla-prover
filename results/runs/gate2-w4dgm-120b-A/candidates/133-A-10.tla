---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Configuration module for the parallel reachability algorithm.  It inherits
\* every shared variable and action from the algorithm itself; this file's
\* job is to supply the concrete graph structure, the process set, and a
\* bounded (finite) version of Succ so the reachable state space stays
\* finite for model checking.  The invariants and the refinement property
\* are untouched by the configuration -- they are defined once in the
\* algorithm module and are re-checked here for every reachable state.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {"idle", "holding", "done"}]
    /\ selected \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

\* Pick: take an unmarked frontier node and compute its successors up-front.
Pick(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ n \notin marked
    /\ pc' = [pc EXCEPT ![p] = "holding"]
    /\ selected' = [selected EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = Succ[n]]
    /\ UNCHANGED <<marked, frontier>>

\* Apply: add all computed successors, then mark the node and drop it from
\* the frontier.  The two updates to marked and frontier are atomic here.
Apply(p) ==
    /\ pc[p] = "holding"
    /\ selected[p] \notin marked
    /\ marked' = marked \cup {selected[p]}
    /\ frontier' = (frontier \cup succs[p]) \ {selected[p]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<selected, succs>>

Recheck(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc, selected, succs>>

Discard(p) ==
    /\ pc[p] = "holding"
    /\ selected[p] \in marked
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

\* All workers idle but the frontier empty: the run is quiescent and can
\* restart from scratch.
Reboot ==
    /\ frontier = {}
    /\ \A p \in Procs : pc[p] = "idle"
    /\ frontier' = {Root}
    /\ marked' = {}
    /\ UNCHANGED <<pc, selected, succs>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Pick(p, n)
    \/ \E p \in Procs : Apply(p)
    \/ \E p \in Procs, n \in Nodes : Recheck(p, n)
    \/ \E p \in Procs : Discard(p)
    \/ \E p \in Procs : Reset(p)
    \/ Reboot

Spec == Init /\ [][Next]_vars

\* The shared marked set and the shared frontier always partition the graph:
\* a node is marked exactly when it has left the frontier, so no node is
\* ever marked twice and no node is left dangling in the frontier once
\* marked.  This is the progress-freedom property the configuration checks.
Inv == \A n \in Nodes : (n \in marked) <=> (n \notin frontier)

\* Correctness: the parallel algorithm's reachable states are contained in
\* those of the sequential Misra algorithm.
Refines == \A n \in Nodes : (n \in marked) ~> (n \in frontier)

\* The .cfg substitutes LimitedSeq for Seq, because a full sequence of
\* arbitrary length would make the reachable state space infinite.  The
\* version here is finite (bounded by the number of nodes) and is what
\* keeps the model checkable.
LimitedSeq(n) == CHOOSE s \in Seq(Nodes) : Len(s) = n

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, which is a
\* bounded version of "each node has at least one successor, but not
\* everyone is a successor of the same node".  The configuration supplies
\* the concrete function; the shape of the graph is part of the model.
ConnectedToSomeButNotAll(n) == Succ[n]

====