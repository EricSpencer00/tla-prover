---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets, ReachableSeq, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "exploring"

Explore(n) ==
    /\ pc = "exploring"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = IF frontier = {n} THEN "done" ELSE pc

Idle ==
    /\ pc = "done"
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"exploring", "done", "idle"}
    /\ (pc = "done" => frontier = {})
    /\ (pc = "idle" => frontier = {})

Inv1 ==
    /\ TypeOK
    /\ \A m \in marked : ReachableFrom(m) \subseteq (marked \cup frontier)

Inv2 == reachableFrom(marked) \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

Inv3 == reachableFrom(Root) = marked \cup reachableFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

PartialCorrectness == (pc = "idle") => (marked = reachableFrom(Root))
====