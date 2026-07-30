---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

RECURSIVE ReachSet(_, _)
ReachSet(S, n) ==
  IF n \in S
    THEN S
    ELSE LET Snew == UNION {ReachSet(S, m) : m \in Succ[n]}
         IN S \cup Snew

ReachableFromRoot == ReachSet({Root}, Root)

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Next ==
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ visited' = visited \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ visited' = visited
          /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier = {} THEN "done" ELSE "running"

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Next)

Inv1 == \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

Inv2 ==
  ReachSet(visited \cup frontier, Root)
    = ReachSet(visited, Root) \cup ReachSet(frontier, Root)

Inv3 == ReachableFromRoot = visited \cup ReachSet(frontier, Root)

PartialCorrectness ==
  (pc = "done") => (visited = ReachableFromRoot)

Termination == (Cardinality(ReachableFromRoot) < Seq) ~> (pc = "done")

====