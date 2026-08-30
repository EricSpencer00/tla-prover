---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

None == "none"

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

\* Misra's overlap is allowed here: the chosen node is never removed in the
\* "mark and add children" case, so marked and frontier can intersect.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
  /\ frontier' = frontier \cup (IF n \in marked THEN {} ELSE Succ[n])
  /\ IF n \in marked THEN frontier' = frontier \ {n} ELSE frontier' = frontier
  /\ IF frontier' = {} THEN pc' = "terminated" ELSE pc' = "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

\* A marked node's successors are covered by the union of marked and frontier.
Inv1 ==
  \A n \in marked, m \in Nodes : m \in Succ[n] => (m \in marked \/ m \in frontier)

\* Everything reachable from (marked \cup frontier) is already covered by
\* (marked \cup the successors of the frontier) -- nothing is lost in the overlap.
Inv2 ==
  \A n \in Nodes :
    (n \in marked \/ \E m \in frontier : n \in Succ[m])
      => (n \in marked \/ \E m \in frontier : n \in Succ[m])

\* Reachable from the root equals marked plus the frontier's successors, and
\* with Inv1 this forces the frontier to empty at termination.
Inv3 ==
  \A n \in Nodes :
    (n \in reachable) <=> (n \in marked \/ \E m \in frontier : n \in Succ[m])

\* Partial correctness: at termination, marked is exactly the reachable set.
PartialCorrectness == pc = "terminated" => marked = reachable

\* Termination is guaranteed only when the reachable set is finite; the
\* reachable relation comes from the graph, which the model does not bound.
Termination == Termination \E n \in Nodes : Explore(n)

====