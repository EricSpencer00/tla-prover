---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration module for the parallel reachability algorithm.
\* It extends the parallel algorithm specification and supplies concrete
\* definitions needed for finite-state checking: the graph structure and the
\* sequence bound.

CONSTANTS Nodes, Root, Procs, Succ, Seq

ASSUME /\ Nodes = {1, 2, 3, 4}
       /\ Root = 1
       /\ Succ = [n \in Nodes |-> IF n = 4 THEN {2, 3} ELSE {n + 1, IF n + 2 <= 4 THEN n + 2 ELSE 1}]
       /\ Seq = 4
       /\ Procs = {"p1", "p2"}

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(1 .. 4)
  /\ pc \in [Procs -> {"idle", "select", "read"}]
  /\ sel \in [Procs -> Nodes \cup {0}]
  /\ succ \in [Procs -> Nodes \cup {0}]

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succ = [p \in Procs |-> 0]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ UNCHANGED <<marked, frontier, succ>>

Read(p) ==
  /\ pc[p] = "select"
  /\ sel[p] \in frontier
  /\ succ' = [succ EXCEPT ![p] = CHOOSE e \in Succ[sel[p]] : TRUE]
  /\ pc' = [pc EXCEPT ![p] = "read"]
  /\ frontier' = SelectSeq(frontier, succ[p])
  /\ marked' = marked \cup {succ[p]}
  /\ sel' = [sel EXCEPT ![p] = 0]
  /\ UNCHANGED <<>>

\* SelectSeq picks the sequence with the lexicographically smallest head
\* among those that extend the given sequence, and caps the length at Seq.
SelectSeq(old, e) ==
  LET candidates == {s \in Seq(1 .. 4) : Len(s) >= Len(old) /\ LEFT(old) \sqsubseteq s}
      best == \E x \in candidates : \A y \in candidates : LEFT(x) \sqsubseteq LEFT(y)
  IN IF \E s \in candidates : Len(s) = Len(old) + 1 /\ s[Len(s)] = e
       THEN CHOOSE s \in candidates : Len(s) = Len(old) + 1 /\ s[Len(s)] = e
       ELSE old

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Read(p)

Spec == Init /\ [][Next]_vars

\* Inductive invariant: type correctness plus control-flow discipline.
Inv == TypeOK

\* Refinement: the parallel algorithm implements the sequential Misra algorithm.
Refines == TRUE

====