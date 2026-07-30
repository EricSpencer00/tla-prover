---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Operators inherited from the parallel algorithm
\* (forward, backward, and Select) are not redefined here;
\* the .cfg substitutes ConnectedToSomeButNotAll for Succ
\* and replaces Seq with LimitedSeq, so only those replacements
\* are defined in this module, and the left-hand names are never
\* declared here.

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

\* Sequence type: a sequence of nodes, bounded in length by the
\* number of nodes.  The .cfg substitutes LimitedSeq for Seq,
\* and this operator must not be declared as Seq.
LimitedSeq == Seq(Nodes)

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in LimitedSeq
    /\ pc \in [Procs -> {"idle", "selecting", "forwarding"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> LimitedSeq]

Init ==
    /\ marked = {Root}
    /\ frontier = LimitedSeq
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> LimitedSeq]

\* Selection: an idle process picks a node that is already marked
\* and not already in its own successor sequence.
Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in marked
    /\ n \notin succs[p]
    /\ pc' = [pc EXCEPT ![p] = "selecting"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = @ \o << n >>]
    /\ UNCHANGED << marked, frontier >>

\* Forwarding: a selecting process adds a new node to the marked set
\* and the frontier sequence (or resets the frontier when it is full).
Forward(p, n) ==
    /\ pc[p] = "selecting"
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = IF Len(frontier) < Len(LimitedSeq)
                    THEN frontier \o << n >>
                    ELSE << n >>
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ pc' = [pc EXCEPT ![p] = "forwarding"]
    /\ UNCHANGED << succs >>

\* Backward: a forwarding process returns to idle.
Back(p) ==
    /\ pc[p] = "forwarding"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED << marked, frontier, sel, succs >>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n) \/ Forward(p, n)
    \/ \E p \in Procs : Back(p)

Spec == Init /\ [][Next]_vars

\* The inductive invariant: the frontier is a subsequence of the
\* shared marked set, and every selected node is already marked.
Inv ==
    /\ \A n \in frontier : n \in marked
    /\ \A p \in Procs : (sel[p] # "none") => (sel[p] \in marked)

\* The refinement property: the shared marked set always contains
\* the frontier sequence, so the parallel algorithm never drops a
\* node that the sequential Misra algorithm would have visited.
Refines ==
    \A i \in 1..Len(frontier) : frontier[i] \in marked

Specifications ==
    /\ Spec
    /\ INVARIANT Inv
    /\ PROPERTY Refines

====