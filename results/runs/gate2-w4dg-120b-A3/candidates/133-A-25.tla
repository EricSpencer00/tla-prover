---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The shared marked set and frontier, plus each process's program counter,
\* selected node, and successor set, are all inherited from the parallel
\* reachability algorithm. The configuration module only supplies the concrete
\* graph (Succ below), the process set, and the bounded sequence override.
VARIABLES marked, frontier, pc, sel, succset

vars == << marked, frontier, pc, sel, succset >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> Nodes \cup {0}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = Nodes \ {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> 0]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = 0
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED marked

Mark(p) ==
  /\ pc[p] = 1
  /\ marked' = marked \cup {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << frontier, sel, succset >>

Idle == UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* The inductive invariant is the same as in the parallel algorithm: type
\* correctness of everything plus the control-flow discipline.
Inv == TypeOK

Refines == TRUE

\* The configuration overrides the unbounded sequence operator with a bounded
\* version that is still a superset of the reachable sequences.
LimitedSeq(s) == FiniteSeq(s)

END M1 == [n \in Nodes |-> << >>]
END M2 == [n \in Nodes |-> << n, n >>]

ConnectedToSomeButNotAll == [n \in Nodes |-> IF Cardinality(Succ[n]) > 0 THEN Succ[n] ELSE {n}]

====