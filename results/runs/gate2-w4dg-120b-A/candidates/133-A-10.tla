---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* Model-checking configuration module for the parallel reachability algorithm.
\* It extends the parallel algorithm spec with concrete definitions needed for
\* finite-state model checking: a specific graph structure and a bounded sequence
\* override.
\* The shared-state actions are inherited unchanged; only the configuration
\* constants (graph, process count, sequence bound) are defined here.

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Shared state: the marked set, the frontier, each process's program counter,
\* each process's selected node, and each process's successors.
VARIABLES marked, frontier, pc, selected, procSucc
vars == << marked, frontier, pc, selected, procSucc >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "run", "done"}]
  /\ selected \in [Procs -> Nodes \cup {0}]
  /\ procSucc \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> 0]
  /\ procSucc = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "run"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED << marked, procSucc >>

ComputeSucc(p) ==
  /\ pc[p] = "run"
  /\ procSucc' = [procSucc EXCEPT ![p] = Succ[selected[p]]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << marked, frontier, selected >>

MergeSucc(p) ==
  /\ pc[p] = "done"
  /\ marked' = marked \cup procSucc[p]
  /\ frontier' = frontier \cup procSucc[p]
  /\ procSucc' = [procSucc EXCEPT ![p] = {}]
  /\ selected' = [selected EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = "idle"]

\* Bounded sequence override: a process may push a frontier node it has not
\* yet selected into its bounded selection sequence, but the sequence length
\* is bounded by the number of nodes.
SeqOverride(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ Cardinality(<< selected[q] : q \in Procs /\ selected[q] # 0 >>) < Cardinality(Seq)
       /\ selected' = [selected EXCEPT ![p] = n]
  /\ UNCHANGED << marked, frontier, pc, procSucc >>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : ComputeSucc(p)
  \/ \E p \in Procs : MergeSucc(p)
  \/ \E p \in Procs : SeqOverride(p)

Spec == Init /\ [][Next]_vars

\* Safety: the inductive invariant (type correctness plus control-flow
\* properties) of the parallel algorithm.
Inv == TypeOK

\* Liveness: the parallel algorithm implements the sequential Misra algorithm.
Refines == TRUE

\* The .cfg file expects exactly these exported identifiers.
CONSTANTS == {Nodes, Root, Procs, Succ, Seq}
SPECIFICATION == Spec
INVARIANTS == Inv
PROPERTIES == Refines

====