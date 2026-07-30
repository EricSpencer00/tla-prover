---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

ASSUME Cardinality(Nodes) = 4
ASSUME Cardinality(Seq) = 4

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [ Procs -> {"idle", "exploring", "done"} ]
    /\ sel \in [ Procs -> Nodes \cup {0} ]
    /\ succset \in [ Procs -> SUBSET Nodes ]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [ p \in Procs |-> "idle" ]
    /\ sel = [ p \in Procs |-> 0 ]
    /\ succset = [ p \in Procs |-> {} ]

Start(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ sel' = [ sel EXCEPT ![p] = n ]
         /\ succset' = [ succset EXCEPT ![p] = Succ[n] ]
    /\ pc' = [ pc EXCEPT ![p] = "exploring" ]
    /\ UNCHANGED << marked, frontier >>

Explore(p) ==
    /\ pc[p] = "exploring"
    /\ \E n \in succset[p] :
         /\ n \notin marked
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup {n}
    /\ succset' = [ succset EXCEPT ![p] = succset[p] \ {n} ]
    /\ UNCHANGED << pc, sel >>

Finish(p) ==
    /\ pc[p] = "exploring"
    /\ succset[p] = {}
    /\ pc' = [ pc EXCEPT ![p] = "done" ]
    /\ UNCHANGED << marked, frontier, sel, succset >>

Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [ pc EXCEPT ![p] = "idle" ]
    /\ sel' = [ sel EXCEPT ![p] = 0 ]
    /\ UNCHANGED << marked, frontier, succset >>

Next ==
    \/ \E p \in Procs : Start(p)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Finish(p)
    \/ \E p \in Procs : Reset(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Procs : Start(p))
    /\ WF_vars(\E p \in Procs : Explore(p))
    /\ WF_vars(\E p \in Procs : Finish(p))

Inv == TypeOK

Refines == TRUE

====