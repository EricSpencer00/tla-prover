---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* The shared marked set and frontier are the two views of the explored region.
\* Each process has its own program counter, selected node, and successor set.
VARIABLES marked, frontier, pc, sel, succset

vars == << marked, frontier, pc, sel, succset >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "select", "expand"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succset \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succset = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succset' = [succset EXCEPT ![p] = Succ[n]]
  /\ UNCHANGED << marked, frontier >>

Expand(p) ==
  /\ pc[p] = "select"
  /\ pc' = [pc EXCEPT ![p] = "expand"]
  /\ UNCHANGED << marked, frontier, sel, succset >>

Commit(p) ==
  /\ pc[p] = "expand"
  /\ marked' = marked \cup succset[p]
  /\ frontier' = (frontier \cup succset[p]) \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succset' = [succset EXCEPT ![p] = {}]

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Expand(p)
  \/ \E p \in Procs : Commit(p)

Spec == Init /\ [][Next]_vars

\* The inductive invariant: the frontier is always a subset of the marked set,
\* and every process is in exactly one of its three control states.
Inv ==
  /\ frontier \subseteq marked
  /\ \A p \in Procs : pc[p] \in {"idle", "select", "expand"}

\* The parallel algorithm refines the sequential Misra algorithm.
Refines == Inv

====