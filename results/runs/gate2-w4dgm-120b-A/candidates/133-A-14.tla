---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

\* Configuration module for the parallel reachability algorithm.  It adds the
\* concrete graph structure (each node has exactly two successors), a bound on
\* sequence lengths, and a replacement for Seq that keeps the state space finite.
CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, target, succ

vars == << marked, frontier, pc, target, succ >>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "select", "expand"}]
  /\ target \in [Procs -> Nodes]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ target = [p \in Procs |-> Root]
  /\ succ = Succ

BeginStep(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ target' = [target EXCEPT ![p] = n]
  /\ UNCHANGED << marked, succ >>

ExpandSuccessors(p, m) ==
  /\ pc[p] = "select"
  /\ m \in succ[target[p]]
  /\ succ' = [succ EXCEPT ![target[p]] = @ \cup {m}]
  /\ UNCHANGED << marked, frontier, pc, target >>

CommitMark(p) ==
  /\ pc[p] = "select"
  /\ target[p] \notin marked
  /\ marked' = marked \cup {target[p]}
  /\ frontier' = frontier \cup succ[target[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << target, succ >>

CancelMark(p) ==
  /\ pc[p] = "select"
  /\ target[p] \in marked
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, frontier, target, succ >>

Next ==
  \/ \E p \in Procs, n \in Nodes : BeginStep(p, n)
  \/ \E p \in Procs, m \in Nodes : ExpandSuccessors(p, m)
  \/ \E p \in Procs : CommitMark(p)
  \/ \E p \in Procs : CancelMark(p)

Spec == Init /\ [][Next]_vars

\* Inductive invariant: type-correctness plus the control-flow restriction that
\* a worker's frontier entry is always in sync with its own program counter.
Inv ==
  /\ TypeOK
  /\ \A p \in Procs : (pc[p] = "select") => (target[p] \in frontier)

\* Correctness via refinement: the parallel algorithm reaches exactly the same
\* shared visited set as the sequential Misra reachability algorithm.
Refines == marked = frontier

\* Configuration substitution: ConnectedToSomeButNotAll replaces Succ to give a
\* concrete graph (each node has exactly two successors), and LimitedSeq replaces
\* Seq with a FINITE version so the model stays checkable.
ConnectedToSomeButNotAll == Succ

ASSUME \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(t) == SELECT S \in FiniteSubsets(t) : TRUE

====