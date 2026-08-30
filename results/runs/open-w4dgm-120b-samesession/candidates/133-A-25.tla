---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> << >>]

StartWork(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ UNCHANGED marked

Visit(p) ==
    /\ pc[p] = "working"
    /\ succs[p] = << >>
    /\ \E c \in Succ[sel[p]] :
        /\ succs' = [succs EXCEPT ![p] = <<c>>]
        /\ marked' = marked \cup {c}
        /\ frontier' = frontier \cup {c}
    /\ UNCHANGED <<pc, sel>>

Continue(p) ==
    /\ pc[p] = "working"
    /\ succs[p] # << >>
    /\ \E c \in Succ[sel[p]] :
        /\ succs' = [succs EXCEPT ![p] = Append(succs[p], c)]
        /\ marked' = marked \cup {c}
        /\ frontier' = frontier \cup {c}
    /\ UNCHANGED <<pc, sel>>

Finish(p) ==
    /\ pc[p] = "working"
    /\ succs[p] # << >>
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \E p \in Procs :
        \/ \E n \in Nodes : StartWork(p, n)
        \/ Visit(p)
        \/ Continue(p)
        \/ Finish(p)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \cup frontier = Nodes
    /\ marked \cap frontier = {}
    /\ \A p \in Procs :
         /\ pc[p] = "idle" => (sel[p] = "none" /\ succs[p] = << >>)
         /\ pc[p] = "working" => sel[p] \in frontier
    /\ \A p \in Procs : Len(succs[p]) <= Cardinality(Nodes)

Refines ==
    \A p \in Procs : pc[p] = "working" => pc[p] # "idle"

ConnectedToSomeButNotAll(n) ==
    /\ Succ[n] # {}
    /\ Cardinality(Succ[n]) < Cardinality(Nodes)

LimitedSeq ==
    /\ Len(succs) < Cardinality(Nodes)
    /\ succs \in Seq(Nodes)

====