---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ pc' = [pc EXCEPT ![p] = "selecting"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED marked

Explore(p) ==
    /\ pc[p] = "selecting"
    /\ succs' = [succs EXCEPT ![p] = Succ[sel[p]]]
    /\ pc' = [pc EXCEPT ![p] = "exploring"]
    /\ UNCHANGED <<marked, frontier, sel>>

Commit(p) ==
    /\ pc[p] = "exploring"
    /\ marked' = marked \cup {succs[p][1]}
    /\ frontier' = frontier \cup {succs[p][1]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = << >>]

Abandon(p) ==
    /\ pc[p] = "exploring"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Abandon(p)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \cap frontier = {}
    /\ \A p \in Procs : pc[p] = "exploring" => succs[p] # << >>
    /\ \A p \in Procs : pc[p] = "exploring" => succs[p][1] \notin marked

Refines ==
    /\ \A p \in Procs : pc[p] = "idle" => sel[p] = "none"
    /\ \A p \in Procs : pc[p] = "selecting" => sel[p] \in frontier
    /\ \A p \in Procs : pc[p] = "exploring" => succs[p] = Succ[sel[p]]

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == Seq

====