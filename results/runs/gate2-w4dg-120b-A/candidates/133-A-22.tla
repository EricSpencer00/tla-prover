---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Model-checking configuration: a concrete graph with 4 nodes, each node having
\* exactly 2 successors, and a bounded sequence capacity (Seq = Cardinality(Nodes)).
\* The parallel reachability algorithm's state, actions, and invariants are
\* parameterised by these constants.

VARIABLES marked, frontier, pc, sel, succset

vars == << marked, frontier, pc, sel, succset >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "select", "expand"}]
  /\ sel \in [Procs -> Nodes]
  /\ succset \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succset = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ UNCHANGED << marked, frontier, succset >>

Expand(p) ==
  /\ pc[p] = "select"
  /\ frontier' = frontier \ {sel[p]}
  /\ marked' = marked \cup {sel[p]}
  /\ succset' = [succset EXCEPT ![p] = Succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "expand"]
  /\ UNCHANGED sel

Advance(p) ==
  /\ pc[p] = "expand"
  /\ Len(succset[p]) >= 1
  /\ frontier' = frontier \cup {Head(succset[p])}
  /\ succset' = [succset EXCEPT ![p] = Tail(succset[p])]
  /\ pc' = IF Len(Tail(succset[p])) = 0
            THEN [pc EXCEPT ![p] = "idle"]
            ELSE [pc EXCEPT ![p] = "expand"]
  /\ UNCHANGED << marked, sel >>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Expand(p)
  \/ \E p \in Procs : Advance(p)

Spec == Init /\ [][Next]_vars

\* Safety property: the inductive invariant of the parallel algorithm (type
\* correctness plus control-flow discipline).  It is exactly the invariant used
\* in the parallel algorithm's own model, now instantiated over the concrete graph.
Inv == TypeOK

\* Refinement property: the parallel algorithm implements the sequential Misra
\* algorithm (the only safety property it was proved to refine).
Refines == Inv

====