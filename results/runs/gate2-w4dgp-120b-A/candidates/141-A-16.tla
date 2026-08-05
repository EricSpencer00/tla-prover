---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc
vars == <<visited, frontier, pc>>

Alive == "alive"
Done == "done"

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {Alive, Done}

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = Alive

Explore ==
    /\ pc = Alive
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ /\ n \notin visited
            /\ visited' = visited \cup {n}
            /\ frontier' = frontier \cup Succ[n]
         \/ /\ n \in visited
            /\ frontier' = frontier \ {n}
            /\ visited' = visited
    /\ pc' = Alive

Terminate ==
    /\ pc = Alive
    /\ frontier = {}
    /\ pc' = Done
    /\ UNCHANGED <<visited, frontier>>

Next_ == Explore \/ Terminate

Spec == Init /\ [][Next_]_vars /\ WF_vars(Explore)

Inv1 == \A n \in visited : Succ[n] \subseteq (visited \cup frontier)

Inv2 == {n \in Nodes : (\E m \in frontier : n \in Succ[m])}
            \cup visited = {n \in Nodes : (\E m \in frontier \cup visited : n \in Succ[m])}

Inv3 == {n \in Nodes : (\E m \in frontier \cup visited : n \in Succ[m])} = visited \cup frontier

PartialCorrectness == (pc = Done) => (visited = {n \in Nodes : (\E m \in visited : n \in Succ[m])})

Termination == (pc = Alive) ~> (pc = Done)

====