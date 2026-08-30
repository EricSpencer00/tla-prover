---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* Image of a set under the neighbor relation, using the concrete bound.
ConnectedToSomeButNotAll(N) == { y \in Nodes : \E x \in N : y \in Succ[x] }

VARIABLES marked, frontier, pc, sel, succ

vars == << marked, frontier, pc, sel, succ >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "selecting", "expanding"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succ \in [Nodes -> SUBSET Nodes]

\* The inductive invariant from the parallel algorithm: type correctness plus
\* the control-flow discipline about frontier and marked.
Invariant ==
    /\ TypeOK
    /\ frontier \subseteq Nodes
    /\ marked \cap frontier = {}
    /\ \A p \in Procs : pc[p] = "selecting" => sel[p] \in frontier
    /\ \A p \in Procs : pc[p] = "expanding" => succ[p] \subseteq ConnectedToSomeButNotAll({sel[p]})

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succ = [n \in Nodes |-> Succ[n]]

Select ==
    /\ \E p \in Procs, n \in frontier :
         /\ pc[p] = "idle"
         /\ pc' = [pc EXCEPT ![p] = "selecting"]
         /\ sel' = [sel EXCEPT ![p] = n]
    /\ UNCHANGED << marked, frontier, succ >>

Expand ==
    /\ \E p \in Procs :
         /\ pc[p] = "selecting"
         /\ pc' = [pc EXCEPT ![p] = "expanding"]
         /\ succ' = [succ EXCEPT ![p] = ConnectedToSomeButNotAll({sel[p]})]
         /\ frontier' = frontier \ {sel[p]}
    /\ UNCHANGED << marked, sel >>

Commit ==
    /\ \E p \in Procs :
         /\ pc[p] = "expanding"
         /\ marked' = marked \union succ[p]
         /\ frontier' = frontier \union succ[p]
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ succ' = [succ EXCEPT ![p] = {}]
    /\ UNCHANGED sel

Finish ==
    /\ \E p \in Procs :
         /\ pc[p] = "selecting"
         /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED << marked, frontier, sel, succ >>

Next == Select \/ Expand \/ Commit \/ Finish

Spec == Init /\ [][Next]_vars

\* The refinement property: every node the sequential Misra algorithm would
\* mark is also marked by the parallel algorithm's shared set.
Refines == marked = ConnectedToSomeButNotAll({Root})

====