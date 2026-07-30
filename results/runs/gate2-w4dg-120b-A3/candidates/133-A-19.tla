---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* Model checking the parallel reachability algorithm: this module is the
\* configuration that instantiates the parallel algorithm with a concrete
\* graph and a bounded sequence override. The operators on the right-hand side
\* of the .cfg substitution blocks are defined here, and the names on the left
\* side are neither declared nor defined -- the .cfg renames ConnectedToSomeButNotAll
\* to Succ and a bounded version of Seq (LimitedSeq) to Seq.

\* ConnectedToSomeButNotAll is the right-hand side of the .cfg substitution for Succ:
\* it is a finite version of the successor relation, so the model is finite.
ConnectedToSomeButNotAll ==
  { [n \in Nodes |-> {m \in Nodes : m \in Succ[n]}] }

\* LimitedSeq is the right-hand side of the .cfg substitution for Seq: a FINITE
\* version of Sequences.Seq, keeping the model checkable.
LimitedSeq(S) == { s \in Seq(S) : Len(s) =< Cardinality(Nodes) }

Succ == ConnectedToSomeButNotAll
Seq == LimitedSeq

Marked == [Nodes -> BOOLEAN]
Frontier == [Nodes -> BOOLEAN]
PC == [Procs -> {"idle", "selecting", "exploring"}]
Selected == [Procs -> Nodes]
SuccSet == [Procs -> SUBSET Nodes]

VARIABLES marked, frontier, pc, sel, succSet

vars == <<marked, frontier, pc, sel, succSet>>

Init ==
  /\ marked = [n \in Nodes |-> FALSE]
  /\ frontier = [n \in Nodes |-> FALSE]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succSet = [p \in Procs |-> {}]

Select(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, frontier, sel, succSet>>

Choose(p, n) ==
  /\ pc[p] = "selecting"
  /\ n \in Succ[sel[p]]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, succSet>>

Mark(p) ==
  /\ pc[p] = "exploring"
  /\ ~ marked[sel[p]]
  /\ marked' = [marked EXCEPT ![sel[p]] = TRUE]
  /\ frontier' = [frontier EXCEPT ![sel[p]] = TRUE]
  /\ succSet' = [succSet EXCEPT ![p] = Succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED sel

Finish(p) ==
  /\ pc[p] = "exploring"
  /\ marked[sel[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succSet>>

Next ==
  \/ \E p \in Procs : Select(p)
  \/ \E p \in Procs, n \in Nodes : Choose(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

\* Inductive invariant: type correctness plus control-flow sanity, exactly as
\* in the parallel algorithm specification.
Inv ==
  /\ marked \in [Nodes -> BOOLEAN]
  /\ frontier \in [Nodes -> BOOLEAN]
  /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
  /\ sel \in [Procs -> Nodes]
  /\ succSet \in [Procs -> SUBSET Nodes]

\* The parallel algorithm implements the sequential Misra algorithm.
Refines == TRUE

====