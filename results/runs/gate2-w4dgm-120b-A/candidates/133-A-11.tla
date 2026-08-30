---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ sel \in [Procs -> Nodes]
    /\ succ \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> Root]
    /\ succ = [p \in Procs |-> {}]

Begin(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, succ>>

FetchSucc(p) ==
    /\ pc[p] = "working"
    /\ succ[p] = {}
    /\ succ' = [succ EXCEPT ![p] = Succ[sel[p]]]
    /\ UNCHANGED <<marked, frontier, pc, sel>>

MarkReachable(p) ==
    /\ pc[p] = "working"
    /\ succ[p] # {}
    /\ marked' = marked \cup succ[p]
    /\ succ' = [succ EXCEPT ![p] = {}]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<frontier, sel>>

Restart(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

Exploit(n) ==
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ UNCHANGED <<frontier, pc, sel, succ>>

Explore(n) ==
    /\ n \notin marked
    /\ frontier' = frontier \cup {n}
    /\ UNCHANGED <<marked, pc, sel, succ>>

Next ==
    \/ \E n \in Nodes : Exploit(n)
    \/ \E n \in Nodes : Explore(n)
    \/ \E p \in Procs : FetchSucc(p)
    \/ \E p \in Procs : MarkReachable(p)
    \/ \E p \in Procs, n \in Nodes : Begin(p, n)
    \/ \E p \in Procs : Restart(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == \A n \in Nodes : (n \in marked) <=> (\E p \in Procs : n \in succ[p])

ConnectedToSomeButNotAll(x) == Succ[x]

LimitedSeq == Seq
====