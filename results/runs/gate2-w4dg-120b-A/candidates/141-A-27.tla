---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET x == CHOOSE y \in S : TRUE
        succs == Succ[x]
    IN succs \cup ReachFrom(S \ {x} \cup succs)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* (1) Every successor of a marked node is either already marked or promised in
\* the frontier, so no reachable node is left behind.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* (2) The nodes reachable from the combined marked/frontier pool are exactly the
\* nodes reachable from the individual reachable piles' union.
Inv2 ==
  ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)

\* (3) Reachable nodes are precisely the visited pile plus the frontier's fringe.
Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness == ReachFrom({Root}) = marked

Termination == (ReachFrom({Root}) < Cardinality(Nodes)) ~> (pc = "done")
====