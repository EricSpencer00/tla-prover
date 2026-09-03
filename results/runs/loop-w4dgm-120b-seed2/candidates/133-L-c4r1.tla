---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

RangeOf(q) == {q[i] : i \in DOMAIN q}

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "aborted"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> << >>]

Start(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in ConnectedToSomeButNotAll
    /\ n \notin marked
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Load(p, n) ==
    /\ pc[p] = "working"
    /\ succs[p] # << >>
    /\ Len(succs[p]) < Cardinality(Nodes)
    /\ n \in Succ[sel[p]]
    /\ n \notin marked
    /\ succs' = [succs EXCEPT ![p] = Append(succs[p], n)]
    /\ UNCHANGED <<marked, frontier, pc, sel>>

Commit(p) ==
    /\ pc[p] = "working"
    /\ succs[p] # << >>
    /\ marked' = marked \cup RangeOf(succs[p])
    /\ frontier' = frontier \cup RangeOf(succs[p])
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = << >>]

Abort(p) ==
    /\ pc[p] = "working"
    /\ pc' = [pc EXCEPT ![p] = "aborted"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier, sel>>

Retry(p) ==
    /\ pc[p] = "aborted"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs, n \in ConnectedToSomeButNotAll : Start(p, n)
    \/ \E p \in Procs, n \in Nodes : Load(p, n)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Abort(p)
    \/ \E p \in Procs : Retry(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == FrontierIsSubsetOfMarked

FrontierIsSubsetOfMarked ==
    frontier \subseteq marked

LimitedSeq(q) == q
====