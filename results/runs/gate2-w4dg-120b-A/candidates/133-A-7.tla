---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, sur

vars == <<marked, frontier, pc, sel, sur>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "selected", "working", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ sur \in [Procs -> Nodes \cup {"none"}]

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ sur = [p \in Procs |-> "none"]

Select(p) ==
    /\ pc[p] = "idle"
    /\ \E u \in frontier :
         /\ sel' = [sel EXCEPT ![p] = u]
         /\ frontier' = frontier \ {u}
    /\ pc' = [pc EXCEPT ![p] = "selected"]
    /\ UNCHANGED <<marked, sur>>

Explore(p) ==
    /\ pc[p] = "selected"
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED <<marked, frontier, sel, sur>>

Report(p) ==
    /\ pc[p] = "working"
    /\ \E v \in Succ[sel[p]] :
         /\ marked' = marked \cup {v}
         /\ frontier' = frontier \cup {v}
         /\ sur' = [sur EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<sel>>

Reclaim(p) ==
    /\ pc[p] = "done"
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ sur' = [sur EXCEPT ![p] = "none"]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs : Select(p)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Report(p)
    \/ \E p \in Procs : Reclaim(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====