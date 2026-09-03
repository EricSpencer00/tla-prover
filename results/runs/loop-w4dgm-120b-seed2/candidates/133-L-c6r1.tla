---- MODULE MCParReach ----
EXTENDS Naturals, Sequences
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, select, succs

Vars == <<marked, frontier, pc, select, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq(Nodes)
    /\ pc \in [Procs -> {"idle", "reading", "writing"}]
    /\ select \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ select = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

Read(p) ==
    /\ pc[p] = "idle"
    /\ frontier # <<>>
    /\ select' = [select EXCEPT ![p] = Head(frontier)]
    /\ frontier' = Tail(frontier)
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ succs' = [succs EXCEPT ![p] = Succ[Head(frontier)]]
    /\ UNCHANGED marked

Write(p) ==
    /\ pc[p] = "reading"
    /\ marked' = marked \cup succs[p]
    /\ frontier' = Append(frontier, succs[p])
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<select, succs>>

Reset(p) ==
    /\ pc[p] = "writing"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ select' = [select EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Stall(p) ==
    /\ pc[p] \in {"reading", "writing"}
    /\ frontier = <<>>
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ select' = [select EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Next == \E p \in Procs : Read(p) \/ Write(p) \/ Reset(p) \/ Stall(p)

Spec == Init /\ [][Next]_Vars

Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq(Nodes)
    /\ pc \in [Procs -> {"idle", "reading", "writing"}]
    /\ \A p \in Procs : select[p] \in Nodes \cup {"none"}
    /\ \A p \in Procs : succs[p] \subseteq Nodes

Refines == \A p \in Procs : pc[p] \in {"idle", "reading", "writing"}

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====