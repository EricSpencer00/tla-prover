---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

NONE == "none"

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {NONE, "running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Expand(n) == {s \in Nodes : n \in Succ[s]}

\* Either case of the single main action, applied to a nondeterministically
\* chosen frontier node; the overlap (keeping n in frontier) is the variant.
Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ visited' = IF n \in visited
                  THEN visited
                  ELSE visited \cup {n}
  /\ frontier' = IF n \in visited
                   THEN frontier \ {n}
                   ELSE frontier \cup Expand(n)
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next == (\E n \in Nodes: Explore(n)) \/ Terminate

Spec == Init /\ [][Next]_vars

\* A marked node's successors are always accounted for in visited or frontier.
Inv1 ==
  \A n \in visited : Expand(n) \subseteq (visited \cup frontier)

\* The combined reachable set of visited and frontier is closed under expansion.
Inv2 ==
  Expand(visited \cup frontier) \subseteq (visited \cup frontier)

\* Reachable-from-root equals visited plus frontier-reachable.
Inv3 ==
  Reachable(Nodes, Root, Succ) = visited \cup Reachable(Nodes, frontier, Succ)

PartialCorrectness == visited = Reachable(Nodes, Root, Succ)

Termination == (frontier # {}) ~> (frontier = {})

====