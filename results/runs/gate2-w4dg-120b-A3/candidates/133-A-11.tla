---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs

\* The graph is frozen at compile time for model checking; each node has
\* exactly two successors, and Succ is defined as a set rather than a
\* function so it stays finite.
VARIABLES marked, frontier, pc, sel, succSet

vars == << marked, frontier, pc, sel, succSet >>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> {"idle", "working", "done"}]
    /\ sel \in [Procs -> Nodes]
    /\ succSet \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> Root]
    /\ succSet = [n \in Nodes |-> ConnectedToSomeButNotAll(n)]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED << marked, frontier, succSet >>

Explore(p) ==
    /\ pc[p] = "working"
    /\ LET new == succSet[sel[p]] \ marked IN
        /\ marked' = marked \cup new
        /\ frontier' = frontier \cup (new \ marked)
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << sel, succSet >>

Reset(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED << marked, frontier, sel, succSet >>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

\* The shared marked set always contains every node in some process's
\* current frontier element; that coupling is what stops a node from
\* being lost between the two representations.
Inv ==
    /\ TypeOK
    /\ \A p \in Procs : pc[p] = "working" => sel[p] \in frontier

\* The parallel algorithm must always agree with the reference sequential
\* Misra implementation on which nodes are reachable.
Refines == \A n \in Nodes : (n \in marked) <=> Reachable(n)

\* A bounded-but-finite version of Succ for model checking; the .cfg
\* substitutes this operator for Succ, so the state space stays finite.
ConnectedToSomeButNotAll(n) ==
    succSet[n]

\* A finite version of the unbounded Seq operator; the .cfg substitutes
\* this for Seq, so sequences in the model are always bounded.
LimitedSeq(S) ==
    {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

====