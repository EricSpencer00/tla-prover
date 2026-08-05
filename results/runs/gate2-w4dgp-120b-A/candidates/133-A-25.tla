---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

SuccSet(n) == Succ[n]

Init ==
    /\ marked = {Root}
    /\ frontier = SuccSet(Root)
    /\ pc = [p \in Procs |-> 0]
    /\ sel = [p \in Procs |-> 0]
    /\ succs = [p \in Procs |-> << >>]

Bump(n) == IF n < Cardinality(Nodes) THEN n + 1 ELSE n

Mark(p) ==
    /\ pc[p] = 0
    /\ \E x \in frontier :
         /\ sel' = [sel EXCEPT ![p] = x]
         /\ frontier' = frontier \ {x}
    /\ marked' = marked \cup {x}
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ pc' = [pc EXCEPT ![p] = 1]

Plan(p) ==
    /\ pc[p] = 1
    /\ succs' = [succs EXCEPT ![p] = << x \in SuccSet(sel[p]) : x \notin marked >>]
    /\ pc' = [pc EXCEPT ![p] = 2]
    /\ UNCHANGED <<marked, frontier, sel>>

Apply(p) ==
    /\ pc[p] = 2
    /\ frontier' = frontier \cup succs[p]
    /\ pc' = [pc EXCEPT ![p] = 0]
    /\ UNCHANGED <<marked, sel, succs>>

Next == \E p \in Procs : Mark(p) \/ Plan(p) \/ Apply(p)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs : pc[p] \in 0..2
    /\ \A p \in Procs : pc[p] = 1 => sel[p] \in frontier
    /\ \A p \in Procs : pc[p] = 2 => succs[p] = << x \in SuccSet(sel[p]) : x \notin marked >>

Refines == \A n \in Nodes : n \in marked

====