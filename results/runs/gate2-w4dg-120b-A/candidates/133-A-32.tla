---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {"idle", "select", "expand"}]
    /\ sel \in [Procs -> Nodes]
    /\ succset \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> Root]
    /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![p] = "select"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succset>>

Expand(p) ==
    /\ pc[p] = "select"
    /\ marked' = marked \cup Succ[sel[p]]
    /\ frontier' = frontier \cup Succ[sel[p]]
    /\ succset' = [succset EXCEPT ![p] = Succ[sel[p]]]
    /\ pc' = [pc EXCEPT ![p] = "expand"]
    /\ UNCHANGED sel

Complete(p) ==
    /\ pc[p] = "expand"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, sel, succset>>

Next ==
    \/ \E p \in Procs, n \in Nodes: Select(p, n)
    \/ \E p \in Procs: Expand(p)
    \/ \E p \in Procs: Complete(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====