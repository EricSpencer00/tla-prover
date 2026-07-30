---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq
    /\ Cardinality(frontier) <= Cardinality(Nodes)
    /\ pc \in [Procs -> {"idle", "step", "succ", "done"}]
    /\ sel \in [Procs -> Nodes]
    /\ succ \in [Procs -> Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> CHOOSE n \in Nodes : TRUE]
    /\ succ = [p \in Procs |-> CHOOSE n \in Nodes : TRUE]

Step(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ p' = [pc EXCEPT ![p] = "step"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succ>>

Succ(p, m) ==
    /\ pc[p] = "step"
    /\ m \in Succ[sel[p]]
    /\ m \notin marked
    /\ frontier' = Append(frontier, m)
    /\ marked' = marked \cup {m}
    /\ succ' = [succ EXCEPT ![p] = m]
    /\ pc' = [pc EXCEPT ![p] = "succ"]
    /\ UNCHANGED sel

Done(p) ==
    /\ pc[p] \in {"step", "succ"}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Step(p, n)
    \/ \E p \in Procs, m \in Nodes : Succ(p, m)
    \/ \E p \in Procs : Done(p)
    \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

====