---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

(*--algorithm ParallelReachability
variables
    marked = {} ,
    frontier = {Root},
    pc = [p \in Procs |-> "SelectNode"],
    selected = [p \in Procs |-> CHOOSE n \in Nodes : FALSE],
    succset = [p \in Procs |-> {}];
define
    Init ==
        /\ marked = {}
        /\ frontier = {Root}
        /\ pc = [p \in Procs |-> "SelectNode"]
        /\ selected = [p \in Procs |-> CHOOSE n \in Nodes : FALSE]
        /\ succset = [p \in Procs |-> {}];
    SelectNode ==
        /\ \E p \in Procs : pc[p] = "SelectNode" /\ frontier # {}
        /\ \E p \in Procs :
            /\ pc[p] = "SelectNode"
            /\ selected[p] \in frontier
            /\ pc' = [pc EXCEPT ![p] = "LoadSucc"]
            /\ UNCHANGED <<marked, frontier, succset>>
    LoadSucc ==
        /\ \E p \in Procs : pc[p] = "LoadSucc"
        /\ \E p \in Procs :
            /\ pc[p] = "LoadSucc"
            /\ succset' = [succset EXCEPT ![p] = Succ[selected[p]]]
            /\ pc' = [pc EXCEPT ![p] = "UpdateFrontier"]
            /\ UNCHANGED <<marked, frontier, selected>>
    UpdateFrontier ==
        /\ \E p \in Procs : pc[p] = "UpdateFrontier"
        /\ \E p \in Procs :
            /\ pc[p] = "UpdateFrontier"
            /\ frontier' = (frontier \ {selected[p]}) \cup (succset[p] \ marked)
            /\ marked'   = marked \cup {selected[p]}
            /\ pc' = [pc EXCEPT ![p] = "SelectNode"]
            /\ UNCHANGED <<selected, succset>>
    Next ==
        \/ SelectNode
        \/ LoadSucc
        \/ UpdateFrontier;
end define;
variables marked, frontier, pc, selected, succset;
Init == Init;
Next == Next;
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succset>>
====