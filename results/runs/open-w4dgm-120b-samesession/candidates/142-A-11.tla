---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"idle", "active", "done"}

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "idle"

MarkStep == /\ pc \in {"idle", "active"}
            /\ \E n \in frontier:
                 /\ marked' = marked \cup {n}
                 /\ frontier' = frontier \ {n}
            /\ pc' = "active"

ExpandStep == /\ pc \in {"idle", "active"}
              /\ \E n \in marked:
                   frontier' = frontier \cup (Succ(n) \ {n})
              /\ marked' = marked
              /\ pc' = "active"

Stop == /\ pc = "active"
        /\ frontier = {}
        /\ pc' = "done"
        /\ marked' = marked
        /\ frontier' = frontier

Next == MarkStep \/ ExpandStep \/ Stop

Spec == Init /\ [][Next]_vars

Invariant1 == TypeOK /\ \A n \in marked: Succ(n) \subseteq (marked \cup frontier)

Invariant2 == (marked \cup frontier) \cup ReachableFrom(Nodes, frontier)
                = ReachableFrom(Nodes, marked \cup frontier)

Invariant3 == ReachableFrom(Nodes, {Root}) = (marked \cup ReachableFrom(Nodes, frontier))

Invariant4 == (ReachableFrom(Nodes, {Root}) \ frontier) \subseteq marked

Terminating == pc = "done"
Partial == Terminating => (marked = ReachableFrom(Nodes, {Root}))

====