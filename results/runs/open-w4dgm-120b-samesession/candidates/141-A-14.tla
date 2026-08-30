---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* Misra's algorithm: visited (marked) nodes and the frontier may overlap,
\* which is what makes the set update order-free and parallelizable.
\* The single process repeatedly picks a frontier node, marks it, and adds
\* its successors to the frontier (without removing the node), or removes
\* it if already marked. Termination is only guaranteed when the reachable
\* set is finite, so the invariant is partial correctness for any case.
\* The .cfg file injects ConnectedToSomeButNotAll for Succ and a FINITE
\* version of Seq via the operator override for LimitedSeq.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The two cases of the action are options on a nondeterministic choice
\* from the frontier, so the loop's progress does not depend on any order.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ \/ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup Succ[n]
     \/ n \in marked
       /\ frontier' = frontier \ {n}
       /\ marked' = marked
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ marked' = marked
  /\ frontier' = frontier

Next == (\E n \in Nodes: Explore(n)) \/ Terminate

Spec == Init /\ [][Next]_vars

\* Safety: partial correctness via three coupled invariants.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Reachable is defined by SCC closure from a base set via Succ.
Reachable(S) == UNION {LimitedSeq(S)^i : i \in 0..Cardinality(Nodes)}

\* Marked nodes' successors are covered by the closure of marked+frontier.
Inv2 ==
  (marked \cup frontier) \subseteq Reachable(frontier \cup marked)

\* Reachable from the root is exactly marked-plus-what-frontier-can-reach.
Inv3 ==
  Reachable({Root}) = (marked \cup Reachable(frontier))

PartialCorrectness ==
  (pc = "terminated") => (marked = Reachable({Root}))

\* Termination is only promised when the reachable set is finite, so it
\* is a liveness property (fairness) rather than a hard invariant.
Termination ==
  /\ Cardinality(Reachable({Root})) < Infinity
  /\ TRUE

\* The .cfg substitutes ConnectedToSomeButNotAll in for Succ, and
\* overrides the definition of Seq with a finite version, so neither
\* definition is needed here and the "unused" tag keeps TLC quiet.
Succ == ConnectedToSomeButNotAll

SEQ == LimitedSeq

====