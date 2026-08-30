---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* Reachable nodes from a given set; used in the invariants.
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE e \in S : TRUE IN {n} \cup Succ[n] \cup ReachFrom(S \ {n})

VARIABLES marked, frontier, pc

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Explore(n) ==
  /\ n \in frontier
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next ==
  \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "running", "done"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachFrom({Root}))

Termination ==
  WF_vars(Next)

====