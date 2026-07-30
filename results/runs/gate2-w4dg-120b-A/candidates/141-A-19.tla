---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"ready", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "ready"

Explore(n) ==
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {n} /\ n \in marked THEN "done" ELSE "ready"

Next ==
    \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    (\A S \in SUBSET Nodes : (S \cup marked) \cup (Succ[S] \cup frontier) = S \cup (marked \cup frontier))
        => (Succ[S] \cup frontier) \cup marked = Succ[S] \cup frontier \cup marked

Inv3 ==
    Succ[frontier] \cup marked = Succ[marked \cup frontier]

PartialCorrectness ==
    \/ (pc = "done" /\ marked = Succ[marked])
    \/ (pc = "done" /\ frontier = {})

Termination == [] (frontier # {}) ~> (frontier = {})

====