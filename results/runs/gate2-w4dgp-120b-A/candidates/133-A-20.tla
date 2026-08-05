---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succbuf

vars == <<marked, frontier, pc, sel, succbuf>>

StateBound == Cardinality(Nodes)

Nxt(v) == (v + 1) % StateBound
Prev(v) == (v + StateBound - 1) % StateBound

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> 0]
    /\ succbuf = [p \in Procs |-> << >>]

Explore(p) ==
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ \E v \in frontier :
        /\ pc' = [pc EXCEPT ![p] = "working"]
        /\ sel' = [sel EXCEPT ![p] = v]
        /\ succbuf' = [succbuf EXCEPT ![p] = << >>]
        /\ frontier' = frontier \ {v}
    /\ UNCHANGED marked

Load(p) ==
    /\ pc[p] = "working"
    /\ succbuf[p] = << >>
    /\ succbuf' = [succbuf EXCEPT ![p] = <<Succ(sel[p]), Succ(Nxt(sel[p]))>>]
    /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
    /\ pc[p] = "working"
    /\ succbuf[p] # << >>
    /\ \E node \in SeqSelect(succbuf[p], 1) :
        /\ node \notin marked
        /\ marked' = marked \cup {node}
        /\ frontier' = frontier \cup {node}
    /\ succbuf' = [succbuf EXCEPT ![p] = Tail(succbuf[p])]
    /\ UNCHANGED <<pc, sel>>

Finish(p) ==
    /\ pc[p] = "working"
    /\ succbuf[p] = << >>
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, sel, succbuf>>

Idle ==
    /\ \A p \in Procs : pc[p] = "idle"
    /\ marked = Nodes
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Load(p)
    \/ \E p \in Procs : Mark(p)
    \/ \E p \in Procs : Finish(p)
    \/ Idle

Spec == Init /\ [][Next]_vars

Inv == \A p \in Procs : \A n \in 1..StateBound : n <= Len(succbuf[p]) => succbuf[p][n] \in Nodes

Refines == \A u \in Nodes : u \in marked => u = Root \/ \E w \in Nodes : u = Succ(w) \/ u = Succ(Nxt(w))

ConnectedToSomeButNotAll == Succ

LimitedSeq == Seq
====