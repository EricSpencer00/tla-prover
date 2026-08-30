---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"
MaxSeq == Cardinality(Nodes)

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working"}]
    /\ sel \in [Procs -> Nodes \cup {NONE}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> NONE]
    /\ succs = [p \in Procs |-> {}]

StartWork(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ sel' = [sel EXCEPT ![p] = n]
         /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked>>

SelectSucc(p) ==
    /\ pc[p] = "working"
    /\ succs[p] = {}
    /\ \E m \in Succ[sel[p]] : succs' = [succs EXCEPT ![p] = {m}]
    /\ UNCHANGED <<marked, frontier, pc, sel>>

MarkSucc(p) ==
    /\ pc[p] = "working"
    /\ succs[p] # {}
    /\ \E m \in succs[p] :
         /\ marked' = marked \cup {m}
         /\ frontier' = frontier \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = NONE]
    /\ succs' = [succs EXCEPT ![p] = {}]

Next == \E p \in Procs : StartWork(p) \/ SelectSucc(p) \/ MarkSucc(p)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \cap frontier = {}
    /\ marked \cup frontier = Nodes
    /\ \A p \in Procs : pc[p] = "idle" => sel[p] = NONE
    /\ \A p \in Procs : pc[p] = "working" => sel[p] \in Nodes

Refines == \A n \in Nodes : n \in marked

Survives == TRUE

LimitedSeq == Seq

ConnectedToSomeButNotAll == Succ

====