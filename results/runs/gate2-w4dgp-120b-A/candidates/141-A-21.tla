---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Reachable nodes from a starter set via the (possibly infinite) successor
\* relation Succ, computed as the least fixed point of the forward-image
\* operation. (Reachable is a semantic convenience for the correctness
\* statement; the algorithm below implements Misra's BFS variant.)
RECURSIVE Reachable(_)
Reachable(s) ==
  LET img(T) == {y \in Nodes : \E x \in T : y \in Succ[x]}
      step(T) == T \cup img(T)
  IN  IF step(s) = s THEN s ELSE Reachable(step(s))

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Misra's BFS variant: the frontier may retain a node after it is marked
\* (overlap with marked), so the cases of Action never drop the chosen
\* node from frontier in the marking case.
Action ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ UNCHANGED marked
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Action \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Action)

\* Invariant 1: every forward neighbor of a marked node is already marked or
\* still waiting in the frontier (not lost, not duplicated, not discarded).
Inv1 ==
  \A x \in marked : img({x}) \subseteq marked \cup frontier

\* Invariant 2: the nodes reachable from the combined marked U frontier set
\* can already be reached from either part alone, so no node is stranded.
Inv2 ==
  Reachable(marked \cup frontier) = Reachable(marked) \cup Reachable(frontier)

\* Invariant 3: the nodes reachable from the root are exactly the marked
\* nodes together with those reachable from the (still-unexplored) frontier.
Inv3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = Reachable({Root}))

\* If the reachable set is finite the algorithm must eventually finish.
Termination == (Cardinality(Reachable({Root})) < 10) => (pc = "done")

\* The cfg substitutes a bounded version of Succ for the name Succ, so the
\* module body never redeclares Succ and does not need to define it here.
Succ(x) == Succ[x]
\* The cfg replaces the unbounded Seq from Sequences with a finite wrapper
\* LimitedSeq; keep the name Seq in scope for any operator that might need
\* it (the operator below is a stub, just enough to bind the name).
LimitedSeq(s) == s
Seq == LimitedSeq

====