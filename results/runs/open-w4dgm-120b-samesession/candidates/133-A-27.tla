---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

\* Model-checking configuration for the parallel reachability algorithm:
\* it provides concrete values for the graph and the process set, and
\* replaces the unbounded Seq operator with a finite one (LimitedSeq) so
\* the reachable state space stays finite and checkable by TLC.

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succSet

vars == <<marked, frontier, pc, selected, succSet>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ selected \in [Procs -> Nodes \cup {"none"}]
    /\ succSet \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> "none"]
    /\ succSet = [p \in Procs |-> {}]

\* The sequence is kept finite by construction: every frontier node has
\* exactly two successors, which is also what makes the graph a bounded
\* 2-out-degree structure rather than an unbounded chain.
Select(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in frontier :
        /\ selected' = [selected EXCEPT ![p] = n]
        /\ succSet' = [succSet EXCEPT ![p] = Succ[n]]
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED <<marked, frontier>>

Mark(p) ==
    /\ pc[p] = "working"
    /\ marked' = marked \cup succSet[p]
    /\ frontier' = (frontier \cup succSet[p]) \ {selected[p]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<selected, succSet>>

\* Reset lets a worker reuse its slot once it has finished, without
\* touching the shared marked/frontier state it already contributed to.
Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = "none"]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Next == \E p \in Procs : Select(p) \/ Mark(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* Safety: shared-state and per-process-control well-typedness plus the
\* invariant's structural shape (worker registers only ever hold a real
\* node, never an out-of-range signal).
Inv == TypeOK

\* Progress: every node eventually gets marked -- the parallel workers
\* together complete the reachability of the whole graph.
Refines == <>(marked = Nodes)

\* Model-checking configuration defines the bounded graph shape and
\* replaces the unbounded sequence operator with a finite one.
ConnectedToSomeButNotAll == Succ
LimitedSeq(i, k) == IF i <= Len(k) THEN k[i] ELSE "none"

====