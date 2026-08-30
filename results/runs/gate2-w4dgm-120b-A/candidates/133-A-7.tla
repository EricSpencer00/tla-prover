---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

Seqs == UNION {[1..n -> Nodes] : n \in 0..Cardinality(Nodes)}

VARIABLES marked, frontier, pc, select, succs

vars == <<marked, frontier, pc, select, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seqs
    /\ pc \in [Procs -> {"idle", "ready", "working", "done"}]
    /\ select \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = << >>
    /\ pc = [p \in Procs |-> "idle"]
    /\ select = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

Pick(p, u) ==
    /\ pc[p] = "idle"
    /\ u \in frontier
    /\ select' = [select EXCEPT ![p] = u]
    /\ pc' = [pc EXCEPT ![p] = "ready"]
    /\ UNCHANGED <<marked, frontier, succs>>

Explore(p) ==
    /\ pc[p] = "ready"
    /\ succs' = [succs EXCEPT ![p] = Succ[select[p]]]
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED <<marked, frontier, select>>

Mark(p, v) ==
    /\ pc[p] = "working"
    /\ v \in succs[p]
    /\ v \notin marked
    /\ marked' = marked \cup {v}
    /\ frontier' = Append(frontier, v)
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED select

Finish(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ select' = [select EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier, succs>>

Next ==
    \/ \E p \in Procs, u \in frontier : Pick(p, u)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs, v \in Nodes : Mark(p, v)
    \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(s) == s \in Seqs

====