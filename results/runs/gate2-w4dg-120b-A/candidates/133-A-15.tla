---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

\* Control states of the parallel algorithm's workers.
\*   idle: not yet started
\*   working: actively exploring a selected node
\*   done: completed, awaiting next round
States == {"idle", "working", "done"}

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> States]
  /\ sel \in [Procs -> Nodes \cup {"nil"}]
  /\ succSet \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "nil"]
  /\ succSet = [p \in Procs |-> {}]

\* A process starts from idle whenever it is free, selecting a frontier node
\* and loading its successors (guaranteed to exist and be exactly 2).
Start(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succSet' = [succSet EXCEPT ![p] = Succ[n]]
  /\ pc' = [pc EXCEPT ![p] = "working"]

\* A working process explores one of its two successors, appending it to the
\* bounded sequence only while the sequence is below its length bound.
Explore(p) ==
  /\ pc[p] = "working"
  /\ \E n \in succSet[p] :
       /\ Len(Seq) < Cardinality(Nodes)
       /\ Seq' = Append(Seq, n)
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel, succSet>>

\* A done process resets to idle and clears its per-round state.
NextRound(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "nil"]
  /\ succSet' = [succSet EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier, Seq>>

Next ==
  \/ \E p \in Procs : Start(p)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : NextRound(p)

Spec == Init /\ [][Next]_vars

\* The shared-state inductive invariant: the frontier and marked set are
\* always disjoint, each process's program counter is a legal control state,
\* and every worker has a successor set exactly equal to its selected node's
\* successors (or empty when nothing is selected).
Inv ==
  /\ frontier \cap marked = {}
  /\ \A p \in Procs : pc[p] \in States
  /\ \A p \in Procs : sel[p] # "nil" => succSet[p] = Succ[sel[p]]

\* The refinement property: the shared marked set must match the Misra
\* algorithm's sequential visited set exactly. Since the sequential model does
\* not keep a frontier, the two models only agree on what has been reached.
Refines ==
  /\ Cardinality(marked) = Cardinality(Seq)
  /\ frontier = Nodes \ Seq
  /\ marked = Seq

====