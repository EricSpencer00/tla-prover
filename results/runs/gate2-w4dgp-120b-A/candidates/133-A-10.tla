---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

\* The graph structure is a fixed small one: every node has exactly two
\* successors, so the reachability step is always well-defined and never
\* blocks on a node with an empty successor set.
\* The bounded sequence overrides below keep the frontier size and the
\* per-process selection sequence within a finite window, which is what
\* makes exhaustive checking feasible at the given bounds.

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> <<>>]
  /\ succ = Succ

MarkFrontier(p) ==
  /\ pc[p] = 0
  /\ Len(frontier) < Cardinality(Nodes)
  /\ LET n == Head(frontier) IN
       /\ marked' = marked \cup {n}
       /\ frontier' = Tail(frontier)
  /\ succ' = [succ EXCEPT ![n] = succ[n] \cup {n}]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED sel

SelectNext(p, n) ==
  /\ pc[p] = 1
  /\ n \in marked
  /\ Len(sel[p]) < Cardinality(Nodes)
  /\ sel' = [sel EXCEPT ![p] = Append(sel[p], n)]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, succ>>

Propagate(p) ==
  /\ pc[p] = 2
  /\ Len(sel[p]) > 0
  /\ LET n == Head(sel[p]) IN
       /\ frontier' = IF frontier = <<>> THEN <<n>> ELSE Append(frontier, n)
       /\ succ' = [succ EXCEPT ![n] = succ[n] \cup {n}]
  /\ sel' = [sel EXCEPT ![p] = Tail(sel[p])]
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED marked

Next ==
  \/ \E p \in Procs : MarkFrontier(p)
  \/ \E p \in Procs, n \in Nodes : SelectNext(p, n)
  \/ \E p \in Procs : Propagate(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \in Sequences(0..Cardinality(Nodes))
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ \A p \in Procs : sel[p] \in Sequences(0..Cardinality(Nodes))
  /\ \A p \in Procs : \A i \in 1..Len(sel[p]) : sel[p][i] \in Nodes
  /\ succ \in [Nodes -> SUBSET Nodes]

Refines == \A n \in Nodes : n \in marked

\* Bounded version of Seq to keep the model finite; the .cfg substitutes it
\* for the standard library's Seq, which would otherwise admit arbitrary length.
LimitedSeq == {s \in Sequences(Nodes) : Len(s) <= Cardinality(Nodes)}
====