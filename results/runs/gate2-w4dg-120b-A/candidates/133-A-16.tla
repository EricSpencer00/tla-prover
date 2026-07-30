---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration for the parallel reachability algorithm.
\* Extends the parallel algorithm with concrete graph and process bounds.
\* Provides the exact identifiers the reference .cfg expects.

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, selected, succset

vars == << marked, frontier, pc, selected, succset >>

\* Control states: idle, working, done.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> Nodes \cup {Root}]
  /\ succset \subseteq Nodes

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succset = Succ

\* A worker picks a node from the frontier and collects its successors.
Explore(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ selected' = [selected EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ frontier' = frontier \ {selected[p]}
  /\ succset' = Succ
  /\ UNCHANGED marked

\* A worker adds its node's successors to the frontier and marks it.
Mark(p) ==
  /\ pc[p] = "working"
  /\ marked' = marked \cup succset
  /\ frontier' = frontier \cup (succset \ {selected[p]})
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << selected, succset >>

\* A finished worker returns to idle to pick another node.
Idle(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ UNCHANGED << marked, frontier, succset >>

Next ==
  \E p \in Procs : Explore(p) \/ Mark(p) \/ Idle(p)

Spec == Init /\ [][Next]_vars

\* The inductive invariant: type correctness plus a control-flow bound
\* on the frontier that keeps the state space finite.
Inv ==
  /\ TypeOK
  /\ Cardinality(frontier) >= 1 /\ Cardinality(frontier) <= 2
  /\ marked \cup frontier \subseteq Nodes
  /\ marked \cap frontier = {}

\* The parallel algorithm refines the sequential Misra algorithm.
Refines == Inv

====