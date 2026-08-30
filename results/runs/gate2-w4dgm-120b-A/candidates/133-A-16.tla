---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

Succs(n) == Succ[n]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> Root]
    /\ succs = [p \in Procs |-> << >>]

Acquire(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ selected' = [selected EXCEPT ![p] = n]
    /\ pc' = [pc EXCEPT ![p] = "selected"]
    /\ succs' = [succs EXCEPT ![p] = << >>]

Advance(p, m) ==
    /\ pc[p] = "selected"
    /\ Len(succs[p]) < Cardinality(Nodes)
    /\ m \in Succs(selected[p])
    /\ succs' = [succs EXCEPT ![p] = Append(succs[p], m)]
    /\ pc' = [pc EXCEPT ![p] = IF Len(succs[p]) + 1 = Cardinality(Nodes) THEN "done" ELSE "selected"]
    /\ UNCHANGED <<marked, frontier, selected>>

Backtrack(p) ==
    /\ pc[p] = "selected"
    /\ succs[p] # << >>
    /\ pc' = [pc EXCEPT ![p] = IF Len(succs[p]) = 1 THEN "idle" ELSE "selected"]
    /\ succs' = [succs EXCEPT ![p] = IF Len(succs[p]) <= 1 THEN << >> ELSE Head(succs[p])]
    /\ UNCHANGED <<marked, frontier, selected>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Acquire(p, n)
    \/ \E p \in Procs, m \in Nodes : Advance(p, m)
    \/ \E p \in Procs : Backtrack(p)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ frontier \cap marked = {}
    /\ frontier \cup marked = Nodes
    /\ \A p \in Procs :
         /\ pc[p] \in {"idle", "selected", "done"}
         /\ selected[p] \in Nodes
         /\ Len(succs[p]) <= Cardinality(Nodes)
         /\ \A i \in 1..Len(succs[p]) : succs[p][i] \in Succs(selected[p])

Refines ==
    \A p \in Procs :
        /\ pc[p] = "selected" => frontier \subseteq marked
        /\ pc[p] = "done" => frontier = {}

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====