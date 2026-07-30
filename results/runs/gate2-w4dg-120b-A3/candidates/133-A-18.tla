---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Model checking overrides the unconstrained sequence operator from Sequences
\* with a finite (bounded) version that stays within the node set.
\* The operator name on the left is FixedSeq; the .cfg substitutes it for Seq.
FixedSeq(d) == CHOOSE s \in [Nat -> Nodes] :
                    /\ \A k \in Nat : s[k] = d
                    /\ \A i \in Nat : \A j \in Nat : (s[i] = s[j] => j <= i)
                    /\ Cardinality({k \in Nat : s[k] # d}) = Cardinality(Nodes)

VARIABLES mark, frontier, pc, sel, succs

vars == <<mark, frontier, pc, sel, succs>>

\* The graph is fixed: each node has exactly two successors, and Root is the
\* only initially marked node.
Init ==
  /\ mark = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

\* The parallel reachability algorithm: mark a successor and push it onto the
\* process's bounded path sequence (FixedSeq) if it is not already marked.
Mark(p) ==
  /\ pc[p] = 0
  /\ frontier # {}
  /\ \E y \in Succ(sel[p]) :
       /\ y \notin mark
       /\ mark' = mark \cup {y}
       /\ frontier' = frontier \cup {y}
       /\ sel' = [sel EXCEPT ![p] = y]
       /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {y}]
  /\ pc' = [pc EXCEPT ![p] = 1]

Done(p) ==
  /\ pc[p] = 1
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<mark, frontier, sel, succs>>

Next == \E p \in Procs : Mark(p) \/ Done(p)

\* Type correctness plus the control-flow requirement from the algorithm spec.
Inv ==
  /\ mark \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..1]
  /\ sel \in [Procs -> Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]
  /\ mark \cup frontier = Nodes

\* Every path a worker has taken is a subsequence of the bounded FixedSeq, so
\* no worker ever exceeds the node-bound number of steps.
SeqBound ==
  \A p \in Procs : succs[p] \subseteq FixedSeq(Root)

Spec == Init /\ [][Next]_vars

Refines == Inv /\ SeqBound

====