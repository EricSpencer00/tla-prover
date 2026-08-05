---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "searching", "done", "blocked"}]
    /\ sel \in [Procs -> Nodes \cup {Root}]
    /\ succSet \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> Root]
    /\ succSet = [p \in Procs |-> {}]

StartSearch(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "searching"]
    /\ UNCHANGED <<marked, frontier, sel, succSet>>

Pick(p, n) ==
    /\ pc[p] = "searching"
    /\ n \in Succ[sel[p]]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succSet' = [succSet EXCEPT ![p] = Succ[n]]
    /\ UNCHANGED <<marked, frontier>>

Mark(p) ==
    /\ pc[p] = "done"
    /\ frontier' = frontier \cup succSet[p]
    /\ frontier' \subseteq Nodes
    /\ marked' = marked \cup frontier
    /\ pc' = [pc EXCEPT ![p] = "blocked"]
    /\ UNCHANGED <<sel, succSet>>

Reset(p) ==
    /\ pc[p] \in {"done", "blocked"}
    /\ frontier' = frontier \ {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ succSet' = [succSet EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, sel>>

Next ==
    \/ \E p \in Procs : StartSearch(p)
    \/ \E p \in Procs, n \in Nodes : Pick(p, n)
    \/ \E p \in Procs : Mark(p)
    \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == \A p \in Procs : pc[p] # "searching"

SuccBound == 2

ConnectedToSomeButNotAll == { n \in Nodes : Cardinality(Succ[n]) >= 1 /\ Cardinality(Succ[n]) < SuccBound }

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

====