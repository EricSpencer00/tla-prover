---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

\* Finite override of the usually-infinite Sequence type, needed for model checking.
\* The name Seq itself is not redeclared here; it is substituted by the .cfg from
\* this definition of LimitedSeq, which keeps the same shape but makes it finite.
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

More == IF pc = "checking" THEN "marking" ELSE "checking"
Stage == IF pc = "checking" THEN "marking" ELSE "checking"

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"checking", "marking"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "checking"

Mark(n) ==
  /\ pc = "checking"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup (Succ[n] \ {n})
  /\ pc' = More

Discard(n) ==
  /\ pc = "checking"
  /\ n \in frontier
  /\ n \in marked
  /\ frontier' = frontier \ {n}
  /\ pc' = More

Toggle ==
  /\ pc \in {"checking", "marking"}
  /\ pc' = More
  /\ UNCHANGED <<marked, frontier>>

Complete ==
  /\ frontier = {}
  /\ pc = "checking"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Mark(n) \/ Discard(n)
  \/ Toggle
  \/ Complete

Spec == Init /\ [][Next]_vars

\* The marked set is closed under successors: every node it contains points only to
\* nodes already marked, so no marked node lies on a frontier pointing outward.
Inv1 == \A n \in marked : Succ[n] \subseteq marked

\* Reachability is partitioned: the visited marked nodes and the unvisited frontier
\* nodes never overlap.
Inv2 == marked \cap frontier = {}

\* The visited set and the frontier together cover everything reachable from the root.
Inv3 == marked \cup frontier = {n \in Nodes : \E s \in LimitedSeq : s[1] = Root /\ s[Len(s)] = n}

\* Partial correctness: reaching a quiescent frontier means the reachable set is
\* exactly the marked set, so nothing reachable is left unmarked.
PartialCorrectness ==
  (frontier = {}) => (marked = {n \in Nodes : \E s \in LimitedSeq : s[1] = Root /\ s[Len(s)] = n})

Termination == []<>(frontier = {})

====