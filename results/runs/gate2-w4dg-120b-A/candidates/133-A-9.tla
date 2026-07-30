---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq
    /\ Cardinality(frontier) <= Cardinality(Nodes)
    /\ pc \in [Procs -> {"idle", "select", "explore", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succ \in [Procs -> Nodes \cup {"none"}]

Init ==
    /\ marked = {Root}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succ = [p \in Procs |-> "none"]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![p] = "select"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succ>>

Explore(p) ==
    /\ pc[p] = "select"
    /\ sel[p] \in frontier
    /\ frontier' = Append(frontier, sel[p])
    /\ marked' = marked \cup Succ[sel[p]]
    /\ pc' = [pc EXCEPT ![p] = "explore"]
    /\ succ' = [succ EXCEPT ![p] = CHOOSE w \in Succ[sel[p]] : TRUE]
    /\ UNCHANGED <<sel>>

Done(p) ==
    /\ pc[p] = "explore"
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succ' = [succ EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ \A p \in Procs : pc[p] = "done"
    /\ marked' = {Root}
    /\ frontier' = <<Root>>
    /\ pc' = [p \in Procs |-> "idle"]
    /\ sel' = [p \in Procs |-> "none"]
    /\ succ' = [p \in Procs |-> "none"]

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Done(p)
    \/ Reset

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines ==
    /\ \A p \in Procs : pc[p] \in {"idle", "select", "explore", "done"}
    /\ frontier \in Seq
    /\ Cardinality(frontier) <= Cardinality(Nodes)
====