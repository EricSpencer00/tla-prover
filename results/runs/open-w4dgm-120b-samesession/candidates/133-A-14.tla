---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Procs, Root

Succ == [n \in Nodes |-> ConnectedToSomeButNotAll[n]]

MaxLen == Cardinality(Nodes)

VARIABLES marked, frontier, pc, chosen, succs

vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "reading", "active", "done"}]
    /\ chosen \in [Procs -> Nodes]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ chosen = [p \in Procs |-> Root]
    /\ succs = [p \in Procs |-> {}]

Read(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ chosen' = [chosen EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succs>>

Expand(p) ==
    /\ pc[p] = "reading"
    /\ frontier' = frontier \cup Succ[chosen[p]]
    /\ pc' = [pc EXCEPT ![p] = "active"]
    /\ succs' = [succs EXCEPT ![p] = Succ[chosen[p]]]
    /\ UNCHANGED <<marked, chosen>>

Mark(p) ==
    /\ pc[p] \in {"reading", "active"}
    /\ marked' = marked \cup {chosen[p]}
    /\ frontier' = frontier \ {chosen[p]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<chosen, succs>>

Idle(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, chosen, succs>>

Settled ==
    /\ \A p \in Procs : pc[p] = "idle"
    /\ frontier = {}
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs, n \in Nodes : Read(p, n)
    \/ \E p \in Procs : Expand(p)
    \/ \E p \in Procs : Mark(p)
    \/ \E p \in Procs : Idle(p)
    \/ Settled

Spec == Init /\ [][Next]_vars

Inv ==
    /\ marked \cap frontier = {}
    /\ \A p \in Procs : (pc[p] = "reading") => (chosen[p] \in frontier)
    /\ \A p \in Procs : (pc[p] = "active") => (succs[p] = Succ[chosen[p]])

Refines ==
    /\ \A p \in Procs : pc[p] = "idle"
    /\ \A p \in Procs : succs[p] = Succ[chosen[p]]

ConnectedToSomeButNotAll ==
    [n \in Nodes |-> {m \in Nodes : n # m /\ m \in succs[n]}]

LimitedSeq(s) ==
    IF Len(s) < MaxLen THEN Append(s, 0) ELSE s

====