---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succ = Succ

TakeStep(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ sel' = [sel EXCEPT ![p] = n]
         /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ UNCHANGED <<marked, succ>>

Work(p) ==
    /\ pc[p] = "working"
    /\ marked' = marked \cup succ[sel[p]]
    /\ frontier' = frontier \cup succ[sel[p]]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<sel, succ>>

Reset(p) ==
    /\ pc[p] = "done"
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, succ>>

Next ==
    \/ \E p \in Procs : TakeStep(p)
    \/ \E p \in Procs : Work(p)
    \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

ConnectedToSomeButNotAll ==
    { n \in Nodes : \E m \in Nodes : m # n /\ m \in succ[n] }

LimitedSeq(n) ==
    IF n = 0 THEN << >>
    ELSE << n >>

====