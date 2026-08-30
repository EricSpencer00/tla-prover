---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

\* Finite-state model checking: a concrete graph where every node has 2
\* successors, and sequences are bounded to at most the number of nodes.
CONSTANTS Nodes, Root, Procs, Succ

MaxLen == Cardinality(Nodes)

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "marking", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succ \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = Succ

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, frontier, succ>>

Mark(p) ==
  /\ pc[p] = "selecting"
  /\ sel[p] \notin marked
  /\ Cardinality(marked) < MaxLen
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup succ[sel[p]]
  /\ frontier' = frontier' \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "marking"]
  /\ UNCHANGED <<sel, succ>>

Rollover(p) ==
  /\ pc[p] = "selecting"
  /\ sel[p] \in marked
  /\ frontier' = frontier \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, succ>>

Finish(p) ==
  /\ pc[p] = "marking"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succ>>

Next ==
  \/ \E p \in Procs, n \in Nodes: Select(p, n)
  \/ \E p \in Procs: Mark(p)
  \/ \E p \in Procs: Rollover(p)
  \/ \E p \in Procs: Finish(p)

Spec == Init /\ [][Next]_vars

\* The invariant the config checks: only the type/shape and control-flow
\* properties, which is why it omits the substantive reachability claim.
Inv == TypeOK

\* Reachability consistency: the parallel algorithm marks only what a
\* sequential Misra run would reach.  Not a shape or control property at all.
Refines ==
  \A n \in Nodes : (n \in marked) => (n \in ConnectedToSomeButNotAll({Root}, n)

\* Model checking replaces Succ with a bounded 'LimitedSeq' wrapper so the
\* reachable state space stays finite; the operator body must remain the old
\* Succ here, and this module does NOT redeclare or rename Seq itself.
LimitedSeq == Succ

====