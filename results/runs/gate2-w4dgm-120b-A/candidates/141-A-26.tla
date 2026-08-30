---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

\* Misra's BFS variant: visited nodes and the frontier may overlap, which
\* is what makes the algorithm parallelizable.
VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Pick any node from the frontier.  If it is not yet visited, add it and
\* hand its successors to the frontier; if it is already visited, drop it.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ IF n \notin visited
       THEN /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ visited' = visited
            /\ frontier' = frontier \ {n}
  /\ pc' = IF (frontier \cup Succ[n]) = {} THEN "done" ELSE "running"

ExploreAny == \E n \in frontier : Explore(n)

Next == ExploreAny

PartialCorrectness ==
  \* Safety: the visited set is exactly the reachable closure of the root.
  visited = {n \in Nodes : (\E m \in {Root} : m ~> n)}

SuccessorClosure(S) ==
  {n \in Nodes : \E m \in S : m ~> n}

\* The three invariants below together imply PartialCorrectness above.
Inv1 ==
  \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

Inv2 ==
  visited \cup frontier = {Root} \cup SuccessorClosure(visited \cup frontier)

Inv3 ==
  SuccessorClosure({Root}) = visited \cup SuccessorClosure(frontier)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(ExploreAny)

Termination ==
  /\ FrontierEventuallyEmpty == (frontier # {}) ~> (frontier = {})
  /\ FrontierEventuallyEmpty

\* The reachable set can be infinite; weak fairness of the loop is what drives
\* termination when it is finite.
Fairness == WF_vars(ExploreAny)

====