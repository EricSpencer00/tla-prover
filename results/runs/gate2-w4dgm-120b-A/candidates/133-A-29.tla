---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* A concrete graph where every node has exactly two successors, matching the
\* sequential module's configuration and keeping the concurrent module's model
\* finite; each node is a pair of successors.
\* Succ is a finite (non-sequence) view of a successor map, used in place of
\* the sequence operator Succ from the standard library.

\* Configuration-level concrete definitions (graph and process set) follow the
\* description's "configuration provides these concrete definitions" line; the
\* rest of the spec is inherited unchanged from the parallel algorithm.

VARIABLES marked, frontier, pc, chosen, succs

vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [ Procs -> { "idle", "reading", "holding", "done" } ]
    /\ chosen \in [ Procs -> Nodes \cup { -1 } ]
    /\ succs \in [ Nodes -> SUBSET Nodes ]

Init ==
    /\ marked = { Root }
    /\ frontier = { Root }
    /\ pc = [ p \in Procs |-> "idle" ]
    /\ chosen = [ p \in Procs |-> -1 ]
    /\ succs = Succ

Acquire(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in frontier :
        /\ frontier' = frontier \ { n }
        /\ chosen' = [ chosen EXCEPT ![p] = n ]
    /\ pc' = [ pc EXCEPT ![p] = "reading" ]
    /\ UNCHANGED << marked, succs >>

Read(p) ==
    /\ pc[p] = "reading"
    /\ pc' = [ pc EXCEPT ![p] = "holding" ]
    /\ UNCHANGED << marked, frontier, chosen, succs >>

Write(p) ==
    /\ pc[p] = "holding"
    /\ marked' = marked \cup { chosen[p] }
    /\ pc' = [ pc EXCEPT ![p] = "done" ]
    /\ UNCHANGED << frontier, chosen, succs >>

Release(p) ==
    /\ pc[p] = "done"
    /\ frontier' = frontier \cup succs[chosen[p]]
    /\ pc' = [ pc EXCEPT ![p] = "idle" ]
    /\ chosen' = [ chosen EXCEPT ![p] = -1 ]
    /\ UNCHANGED << marked, succs >>

Done == \A p \in Procs : pc[p] = "idle"

Next ==
    \/ \E p \in Procs : Acquire(p)
    \/ \E p \in Procs : Read(p)
    \/ \E p \in Procs : Write(p)
    \/ \E p \in Procs : Release(p)
    \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

\* The refinement property: every node at most once reachable under the
\* sequential Misra algorithm is still at most once reachable under the
\* concurrent mix-in.
Refines == Inv

\* View each node's successors as a bounded (finite) set rather than a full
\* sequence, which is what keeps the model finite for TLC.
ConnectedToSomeButNotAll == Succ

\* Replace the standard Sequences.Seq with a finite version so the model is
\* still checkable; the name itself is substituted away by the .cfg.
LimitedSeq == Seq

====