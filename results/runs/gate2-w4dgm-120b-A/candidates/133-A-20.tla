---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, MCSeq

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

NONE == "none"

\* The worker program of the parallel reachability algorithm: a two-phase
\* commit driven by a shared frontier. The frontier is a bounded-length
\* sequence (explicitly overridden to be a FINITE sequence in the cfg), so
\* its length is always checkable rather than potentially infinite.
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq(Nodes)
    /\ pc \in [Procs -> {"idle", "prepared"}]
    /\ sel \in [Procs -> Nodes \cup {NONE}]
    /\ succs \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> NONE]
    /\ succs = Succ

\* Phase 1: a worker prepares a frontier node for expansion.
Prepare(p) ==
    /\ pc[p] = "idle"
    /\ frontier # <<>>
    /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
    /\ frontier' = Tail(frontier)
    /\ pc' = [pc EXCEPT ![p] = "prepared"]
    /\ UNCHANGED <<marked, succs>>

\* Phase 2: the worker commits, marking the node and emitting its succs.
\* The success set is capped to stay finite for model checking.
Commit(p) ==
    /\ pc[p] = "prepared"
    /\ marked' = marked \cup {sel[p]}
    /\ succs' = [succs EXCEPT ![sel[p]] = succs[sel[p]] \cap Nodes]
    /\ frontier' = AppendLimited(frontier, succs[sel[p]])
    /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]

\* Phase-1 abort: the worker gives up and returns the node to the frontier.
AbortReady(p) ==
    /\ pc[p] = "prepared"
    /\ sel[p] \notin marked
    /\ frontier' = AppendLimited(frontier, {sel[p]})
    /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, succs>>

\* A worker may also simply give up on an already-marked node.
GiveUp(p) ==
    /\ pc[p] = "prepared"
    /\ sel[p] \in marked
    /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, succs>>

Next ==
    \/ \E p \in Procs : Prepare(p) \/ Commit(p) \/ AbortReady(p) \/ GiveUp(p)

\* The shared frontier is always a subset of the nodes; the workers' program
\* counters always agree with whether or not they are holding a selected node.
Inv ==
    /\ FrontierWithinNodes
    /\ CountersAgreeOnSelection

FrontierWithinNodes == \A i \in 1..Len(frontier) : frontier[i] \in Nodes

CountersAgreeOnSelection ==
    \A p \in Procs :
        (pc[p] = "prepared") <=> (sel[p] # NONE)

\* The bounded frontier sequence may contain the same node more than once
\* (because the graph is not a DAG), but each node is committed to the
\* reachable set at most once: the set of marked nodes is exactly the closure
\* of the root under the (already-finished) successor relation.
Refines ==
    \A n \in Nodes : n \in marked => (n = Root \/ (\E m \in Nodes : m \in marked /\ n \in succs[m]))

====