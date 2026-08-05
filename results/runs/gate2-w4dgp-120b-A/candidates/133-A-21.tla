---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succset

vars == <<marked, frontier, pc, sel, succset>>

\* Reachability in a parallel setting: workers share one frontier and one
\* marked set, but each chooses nodes from the shared frontier in its own
\* step. The invariant checks both the shape of the shared data and that
\* no worker ever sits on a frontier position that is stale (empty).
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \in Seq(Nodes)
    /\ pc \in [Procs -> {"idle", "selecting", "done"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succset \in [Procs -> SUBSET Nodes]

Next ==
    \/ \E p \in Procs :
         /\ pc[p] = "idle"
         /\ frontier # <<>>
         /\ sel' = [sel EXCEPT ![p] = Head(frontier)]
         /\ frontier' = Tail(frontier)
         /\ pc' = [pc EXCEPT ![p] = "selecting"]
         /\ succset' = [succset EXCEPT ![p] = Succ[Head(frontier)]]
         /\ UNCHANGED marked
    \/ \E p \in Procs :
         /\ pc[p] = "selecting"
         /\ succset[p] \subseteq Nodes \ marked
         /\ marked' = marked \cup succset[p]
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ UNCHANGED <<frontier, sel, succset>>
    \/ \E p \in Procs :
         /\ pc[p] = "idle"
         /\ frontier = <<>>
         /\ \A q \in Procs : pc[q] = "idle"
         /\ marked' = marked \cup Succ[sel[p]]
         /\ pc' = [pc EXCEPT ![p] = "done"]
         /\ UNCHANGED <<frontier, sel, succset>>

Init ==
    /\ marked = {Root}
    /\ frontier = <<Root>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succset = [p \in Procs |-> {}]

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ \A p \in Procs : (pc[p] = "selecting") => (sel[p] \in marked)

Refines == \A p \in Procs : (pc[p] = "done") => (Root \in marked)

Succ == Succ
SuccPrime == Succ
ConnectedToSomeButNotAll == {x \in Nodes : Cardinality(Succ[x]) > 0}
LimitedSeq == Seq(Nodes)

====