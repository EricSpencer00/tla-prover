---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Inherits the full parallel-algorithm specification; this file supplies
\* the concrete configuration constants.
RECURSIVE Succs(_)
Succs(n) == IF n < Cardinality(Nodes) THEN Succ ELSE Succs(n + 1)

VARIABLES mark, frontier, pc, sel, succset

vars == <<mark, frontier, pc, sel, succset>>

TypeOK ==
    /\ mark \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ sel \in [Procs -> 0..Cardinality(Nodes)]
    /\ succset \in [Procs -> Seq]

Init ==
    /\ mark = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> 0]
    /\ succset = [p \in Procs |-> << >>]

Select ==
    /\ \E n \in Nodes :
         /\ frontier[n]
         /\ \E p \in Procs :
              /\ pc[p] = "idle"
              /\ pc' = [pc EXCEPT ![p] = "working"]
              /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<mark, frontier, succset>>

Explore ==
    /\ \E p \in Procs :
         /\ pc[p] = "working"
         /\ \E s \in Succs(sel[p]) :
              /\ mark' = mark \cup {s}
              /\ frontier' = IF s \in frontier THEN frontier ELSE frontier \cup {s}
              /\ succset' = [succset EXCEPT ![p] = IF Len(succset[p]) < Len(Seq) THEN Append(succset[p], s) ELSE succset[p]]
         /\ pc' = [pc EXCEPT ![p] = "done"]
         /\ sel' = [sel EXCEPT ![p] = 0]
    /\ UNCHANGED <<mark, frontier>>

Reset ==
    /\ \E p \in Procs :
         /\ pc[p] = "done"
         /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<mark, frontier, sel, succset>>

Next == Select \/ Explore \/ Reset

Spec == Init /\ [][Next]_vars

Inv ==
    /\ TypeOK
    /\ \A p \in Procs : pc[p] \in {"idle", "working", "done"}
    /\ FrontierSubset == frontier \subseteq Nodes
    /\ MarkNonEmpty == Root \in mark

Refines ==
    /\ FrontierSubset
    /\ MarkNonEmpty

====