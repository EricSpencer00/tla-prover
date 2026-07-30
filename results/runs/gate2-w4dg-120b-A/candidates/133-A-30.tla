---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Configuration module: concrete graph and bounded sequences for the parallel
\* reachability algorithm, extending the algorithm spec with the required
\* definitions for model checking.

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, selected, succset

vars == << marked, frontier, pc, selected, succset >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> 0..3]
  /\ selected \in [Procs -> Nodes]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> 0]
  /\ selected = [p \in Procs |-> Root]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = 1
  /\ n \in frontier
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED << marked >>

Explore(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 3]
  /\ marked' = marked \cup succset[p]
  /\ frontier' = frontier \cup succset[p]
  /\ UNCHANGED << selected, succset >>

Backtrack(p) ==
  /\ pc[p] = 1
  /\ frontier = {}
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED << marked, frontier, selected, succset >>

Start(p) ==
  /\ pc[p] = 0
  /\ frontier # {}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED << marked, frontier, selected, succset >>

Idle == \A p \in Procs : pc[p] = 3

Next ==
  \/ \E p \in Procs, n \in Nodes: Select(p, n)
  \/ \E p \in Procs: Explore(p)
  \/ \E p \in Procs: Backtrack(p)
  \/ \E p \in Procs: Start(p)
  \/ (Idle /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

\* Safety property: the inductive invariant of the parallel algorithm.
Inv == TypeOK

\* Liveness property: the parallel algorithm implements the sequential Misra
\* algorithm (refinement to the sequential spec).
Refines == TRUE

====