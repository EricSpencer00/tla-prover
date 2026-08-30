---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

Vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
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
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED marked

Explore(p) ==
    /\ pc[p] = "working"
    /\ Len(succs[p]) < Cardinality(Nodes)
    /\ succs' = [succs EXCEPT ![p] = Append(succs[p], n) : n \in Succ[sel[p]] \ marked]
    /\ UNCHANGED <<marked, frontier, pc, sel>>

Commit(p) ==
    /\ pc[p] = "working"
    /\ succs[p] # << >>
    /\ marked' = marked \cup {succs[p][1]}
    /\ frontier' = frontier \cup {succs[p][1]}
    /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
    /\ UNCHANGED <<pc, sel>>

Skip(p) ==
    /\ pc[p] = "working"
    /\ Len(succs[p]) > 0
    /\ \A n \in Succ[sel[p]] : n \in marked
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED <<marked, frontier>>

Finish(p) ==
    /\ pc[p] = "working"
    /\ succs[p] = << >>
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier, succs>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Skip(p)
    \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_Vars

Inv ==
    /\ pc["p1"] \in {"idle", "working", "done"}
    /\ pc["p2"] \in {"idle", "working", "done"}
    /\ succs["p1"] = << >>
    /\ succs["p2"] = << >>
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Refines ==
    /\ \A p \in Procs : pc[p] \in {"idle", "working", "done"}
    /\ \A p \in Procs : succs[p] = << >>
    /\ \A p \in Procs : pc[p] = "working" => sel[p] # "none"

ConnectedToSomeButNotAll(n) == Cardinality(Succ[n]) > 0

LimitedSeq == Seq

====