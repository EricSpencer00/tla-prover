---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"
MaxLen == Cardinality(Nodes)

VARIABLES marked, frontier, pc, selected, succs
vars == <<marked, frontier, pc, selected, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "selecting", "acting"}]
    /\ selected \in [Procs -> Nodes \cup {NONE}]
    /\ succs \in [Procs -> Seq(Nodes)]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ selected = [p \in Procs |-> NONE]
    /\ succs = [p \in Procs |-> << >>]

Select(p) ==
    /\ pc[p] = "idle"
    /\ \E n \in frontier :
        /\ selected' = [selected EXCEPT ![p] = n]
        /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "selecting"]
    /\ UNCHANGED <<marked, succs>>

LoadSuccs(p) ==
    /\ pc[p] = "selecting"
    /\ selected[p] \in frontier \cup {NONE}
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ pc' = [pc EXCEPT ![p] = "acting"]
    /\ UNCHANGED <<marked, frontier, selected>>

Act(p) ==
    /\ pc[p] = "acting"
    /\ Len(succs[p]) < MaxLen
    /\ \E m \in ConnectedToSomeButNotAll(selected[p]) :
        /\ succs' = [succs EXCEPT ![p] = Append(succs[p], m)]
    /\ UNCHANGED <<marked, frontier, pc, selected>>

Commit(p) ==
    /\ pc[p] = "acting"
    /\ succs[p] # << >>
    /\ \E i \in 1..Len(succs[p]) :
        /\ marked' = marked \cup {succs[p][i]}
        /\ frontier' = frontier \cup {succs[p][i]}
    /\ succs' = [succs EXCEPT ![p] = << >>]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ selected' = [selected EXCEPT ![p] = NONE]
    /\ UNCHANGED frontier

Done ==
    /\ frontier = {}
    /\ \A p \in Procs : pc[p] = "idle"

Next ==
    \/ \E p \in Procs : Select(p) \/ LoadSuccs(p) \/ Act(p) \/ Commit(p)
    \/ Done

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \cap frontier = {}
    /\ marked \cup frontier = Nodes
    /\ \A p \in Procs :
        /\ pc[p] = "idle" => selected[p] = NONE /\ succs[p] = << >>
        /\ pc[p] = "selecting" => selected[p] \in Nodes /\ succs[p] = << >>
        /\ pc[p] = "acting" => Len(succs[p]) <= MaxLen

Refines == Inv

ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq == Seq

====