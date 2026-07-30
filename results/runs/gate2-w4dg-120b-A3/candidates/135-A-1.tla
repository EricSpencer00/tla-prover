---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "explore"

Explore ==
  /\ pc = "explore"
  /\ frontier # {}
  /\ \E w \in frontier :
       /\ marked' = marked \cup Succ[w]
       /\ frontier' = (frontier \cup Succ[w]) \ {w}
  /\ pc' = IF frontier = {} THEN "done" ELSE "explore"

Next ==
  \/ Explore
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"explore", "done"}

Inv1 ==
  \A x \in marked : \E y \in marked : x \in Succ[y]

Inv2 == marked = {x \in Nodes : \E y \in frontier : x \in Succ[y]}

Inv3 ==
  \A x \in marked : \E y \in frontier : x \in Succ[y]

PartialCorrectness ==
  \A x \in reachable : x \in marked

Termination ==
  <>(pc = "done")

\* Model-checking override: a deterministic graph where each node has exactly
\* 2 successors, and a bounded sequence operator so the state space stays finite.
ConnectedToSomeButNotAll ==
  {n \in Nodes : Cardinality(Succ[n]) = 2}

\* The .cfg substitutes LimitedSeq for the built-in Seq operator from Sequences.
LimitedSeq ==
  \E n \in 1..Cardinality(Nodes) : Sequences.Seq(Nodes)

====