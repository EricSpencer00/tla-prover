---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

NONE == "idle"

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "reading", "computing"}]
    /\ sel \in [Procs -> Nodes \cup {NONE}]
    /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> NONE]
    /\ succ = Succ

Read ==
    /\ \E p \in Procs, n \in frontier :
         /\ pc[p] = "idle"
         /\ pc' = [pc EXCEPT ![p] = "reading"]
         /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succ>>

Compute ==
    /\ \E p \in Procs :
         /\ pc[p] = "reading"
         /\ pc' = [pc EXCEPT ![p] = "computing"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

Mark ==
    /\ \E p \in Procs :
         /\ pc[p] = "computing"
         /\ sel[p] \in frontier
         /\ marked' = marked \cup {sel[p]}
         /\ frontier' = frontier \ {sel[p]}
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ UNCHANGED succ

Spawn ==
    /\ \E p \in Procs :
         /\ pc[p] = "computing"
         /\ frontier' = frontier \cup succ[sel[p]]
    /\ UNCHANGED <<marked, pc, sel, succ>>

Next == Read \/ Compute \/ Mark \/ Spawn

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Init /\ (Next)~> (Init /\ Next)

ConnectedToSomeButNotAll(n) == Cardinality(n) <= 2

LimitedSeq == Seq

====