---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The reachable set as computed by the algorithm: nodes that have been
\* visited (marked) plus nodes still reachable from the frontier buffer.
Reachable == marked \cup ReachFrom(frontier)

\* Fixed-point helper: all nodes reachable from a set, following Succ.
RECURSIVE ReachFrom(_)
ReachFrom(X) ==
  IF X = {} THEN {}
  ELSE LET n == CHOOSE x \in X : TRUE IN X \cup ReachFrom(Succ[n] \cup X \ {n})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"ready", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "ready"

Explore(e) ==
  /\ e \in frontier
  /\ IF e \in marked
       THEN frontier' = frontier \ {e}
       ELSE /\ marked' = marked \cup {e}
            /\ frontier' = frontier \cup Succ[e]
  /\ pc' = "ready"

Retire ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E e \in Nodes : Explore(e)
  \/ Retire

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is already marked or waiting in the frontier.
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* The reachable set from marked \cup frontier is the same as reachable from frontier.
Inv2 == ReachFrom(marked \cup frontier) = ReachFrom(frontier)

\* Reachable nodes are exactly the marked nodes plus the frontier's contribution.
Inv3 == Reachable = marked \cup ReachFrom(frontier)

PartialCorrectness == pc = "done" => Reachable = ReachFrom({Root})

\* Fairness: the loop cannot stall forever if frontier is non-empty.
WF_vars(Next)

Termination == \A e \in Nodes : TRUE => <>(pc = "done")

====