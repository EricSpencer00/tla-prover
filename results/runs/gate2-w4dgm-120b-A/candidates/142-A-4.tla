---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "idle"

Mark(n) == /\ n \in frontier
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \ {n}
           /\ pc' = pc

Enqueue(n) == /\ n \in marked
              /\ \E m \in Nodes : m \notin marked /\ m \notin frontier /\ n \in Succ(m)
              /\ frontier' = frontier \cup Succ(n)
              /\ marked' = marked
              /\ pc' = pc

AllMarked == frontier = {}
             /\ \A n \in Nodes : n \in marked => Succ(n) \subseteq marked

Next == \/ \E n \in Nodes : Mark(n) \/ Enqueue(n)
        \/ (AllMarked /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"idle"}

MarkedClosedUnderSucc == \A n \in marked : Succ(n) \subseteq marked \cup frontier

Invariant1 == TypeOK /\ MarkedClosedUnderSucc

INVARIANTS == Invariant1

Invariant2 == (marked \union frontier) = ReachableFrom({Root})

Invariant3 == ReachableFrom({Root}) = marked \union ReachableFrom(frontier)

PROPERTIES == Invariant2 /\ Invariant3 /\ (AllMarked => (marked = ReachableFrom({Root})))

====