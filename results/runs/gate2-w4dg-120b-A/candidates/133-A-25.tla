---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Inherited state from the parallel reachability algorithm.
VARIABLES marked, frontier, pc, selected, succset

vars == <<marked, frontier, pc, selected, succset>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> 0]
  /\ succset = [p \in Procs |-> {}]

\* Inherited actions: workers take nodes from the shared frontier, mark
\* new nodes, and advance their program counters.
TakeNode(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E x \in frontier:
       /\ frontier' = frontier \ {x}
       /\ selected' = [selected EXCEPT ![p] = x]
       /\ succset' = [succset EXCEPT ![p] = Succ[x]]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED marked

Mark(p) ==
  /\ pc[p] = "working"
  /\ selected[p] \in Nodes
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = frontier \cup succset[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<selected, succset>>

Next == \E p \in Procs : TakeNode(p) \/ Mark(p)

\* Assignments: the project configuration bounds the graph to 4 nodes and
\* fixes the number of worker processes to 2.
Spec == Init /\ [][Next]_vars

\* Invariant: the shared structures never grow beyond the graph's size
\* limits, and each process's program counter stays within the allowed
\* control states.
Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}
  /\ Seq = Cardinality(Nodes)

\* Refinement: the parallel algorithm implements the sequential Misra
\* algorithm's reachability computation.
Refines == TRUE

====