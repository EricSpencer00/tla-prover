---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES visited, frontier, pc
vars == <<visited, frontier, pc>>

Nxt(n) == Succ[n]

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore(n) ==
    /\ n \in frontier
    /\ visited' = visited \cup (IF n \in visited THEN {} ELSE {n})
    /\ frontier' = (frontier \cup (IF n \in visited THEN {} ELSE Nxt[n])) \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<visited, frontier>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ Done

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E n \in Nodes : Explore(n))

Inv1 == \A n \in visited : Nxt[n] \subseteq (visited \cup frontier)
Inv2 == (visited \cup frontier) \cup (Nxt[visited \cup frontier]) = visited \cup Nxt[visited \cup frontier]
Inv3 == (Nodes \ frontier) \cup (Nxt[frontier]) = visited \cup Nxt[visited \cup frontier]

PartialCorrectness == visited = Nodes \ frontier

Termination == pc = "done"

ConnectedToSomeButNotAll(n) == {n}
LimitedSeq == Seq

====