---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

Variable marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* Misra's variant lets the visited and frontier sets overlap.
Explore(n) ==
  /\ n \in frontier
  /\ pc = "running"
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ IF frontier' = {} THEN pc' = "terminated" ELSE pc' = "running"

Next == \E n \in Nodes: Explore(n)

Spec == Init /\ [][Next]_vars

\* Every outgoing edge from a marked node leads somewhere visited or on the frontier.
Inv1 == \A n \in marked: \A m \in Succ[n]: m \in marked \/ m \in frontier

\* The union of marked nodes and frontier-reachable nodes is closed under successors.
Inv2 ==
  /\ (marked \cup frontier \cup (UNION {Succ[n] : n \in marked \cup frontier})
       = Nodes)
  /\ UNCHANGED pc

\* Reachable from the start is exactly the visited plus whatever the frontier brings in.
Inv3 == (UNION {Succ[n] : n \in frontier}) \cup marked = Nodes

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == (frontier # {}) ~> (frontier = {})

\* The reachable set is finite, so the algorithm always eventually stabilizes.
AlwaysEventuallyTerminates ==
  (UNION {Succ[n] : n \in Nodes}) \in FiniteSets
    ~> (frontier = {})

====