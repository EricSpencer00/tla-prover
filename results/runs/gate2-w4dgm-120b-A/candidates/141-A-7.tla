---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

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

ProcessNode(n) ==
    /\ n \in frontier
    /\ IF n \notin visited
       THEN \E suc \in Succ[n]:
              /\ visited' = visited \cup {n}
              /\ frontier' = frontier \cup suc
       ELSE frontier' = frontier \ {n} /\ visited' = visited
    /\ UNCHANGED pc

Done ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<visited, frontier>>

Next == (\E n \in Nodes: ProcessNode(n)) \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E n \in Nodes: ProcessNode(n))

Inv1 == \A n \in visited : (Succ[n] \subseteq visited) \/ (Succ[n] \cap frontier # {})
Inv2 == (visited \cup frontier) = (visited \cup frontier)
Inv3 == (Nodes \ {Root}) = visited \cup frontier

PartialCorrectness ==
    visited \cup frontier = Nodes

Termination == (Nodes \ {Root} # {}) ~> (Nodes \ {Root} = {})
====