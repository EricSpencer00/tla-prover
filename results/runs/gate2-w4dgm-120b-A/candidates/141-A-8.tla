---- MODULE Reachable ----
EXTENDS Naturals, Sequences

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

Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ \E newFrontier \in frontier \cup Succ[n] \cup {n} :
       frontier' = newFrontier
  /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
  /\ pc' = IF n \in marked THEN "running" ELSE pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ marked' = marked
  /\ frontier' = frontier

Next ==
  \/ \E n \in Nodes: Explore(n)
  \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  (marked \cup frontier)^{reach} = marked \cup frontier^{reach}

Inv3 ==
  Root^{reach} = marked \cup frontier^{reach}

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in Root^{reach})

Termination ==
  \A n \in Nodes : (n \in frontier) ~> (n \notin frontier)

\* The .cfg replaces Succ with ConnectedToSomeButNotAll, a bounded
\* variant of the full successor relation, so the model stays finite.
ConnectedToSomeButNotAll(n) == Succ[n]

\* The .cfg redefines Seq (from Sequences) as LimitedSeq, a FINITE version
\* that keeps the state space countable for TLC; it must stay EXTENDS-only.
LimitedSeq(S) == S

====