---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* Misra's algorithm: a BFS variant whose visited- and frontier-sets may
\* overlap, so the two actions below contend for the same nodes and can be
\* replayed in parallel by a separate implementation. The spec below is
\* deliberately written with a single process; correctness does not depend
\* on it.
CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES visited, frontier, pc

TypeOK == /\ visited \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "halted"}

Init == /\ visited = {}
        /\ frontier = {Root}
        /\ pc = "running"

Explore == /\ pc = "running"
           /\ \E n \in frontier :
                \/ (n \notin visited /\ visited' = visited \cup {n}
                                          /\ frontier' = frontier \cup Succ[n])
                \/ (n \in visited /\ frontier' = frontier \ {n})
           /\ pc' = pc

Halt == /\ pc = "running"
        /\ frontier = {}
        /\ pc' = "halted"
        /\ visited' = visited
        /\ frontier' = frontier

Next == Explore \/ Halt

Spec == Init /\ [][Next]_<<visited, frontier, pc>>

\* The three invariants capture reachability: successors of visited nodes
\* are already visited or still pending on the frontier, and visited plus
\* frontier together already reach exactly the reachable set.
Inv1 == \A n \in visited : Succ[n] \subseteq (visited \cup frontier)
Inv2 == Reached(visited \cup frontier) = visited \cup Reached(frontier)
Inv3 == Reached(Nodes) = visited \cup Reached(frontier)

PartialCorrectness == visited = Reached(Nodes)

\* Reachable is finite only when the reachable set is finite; weak fairness
\* of the single Explore action (always enabled while the frontier is
\* non-empty) forces termination once nothing new remains reachable.
Termination == (\E f \in [Nat -> Nodes] : \A k \in Nat : f[k] \in frontier)
                ~> (pc = "halted")
====