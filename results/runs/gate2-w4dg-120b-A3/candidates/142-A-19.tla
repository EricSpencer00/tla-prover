---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachability

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "exploring", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

Explore(n) ==
    /\ pc = "idle"
    /\ frontier = {}
    /\ n \notin marked
    /\ frontier' = frontier \cup {n}
    /\ pc' = "exploring"
    /\ UNCHANGED marked

Mark(v) ==
    /\ pc = "exploring"
    /\ v \in frontier
    /\ v \notin marked
    /\ marked' = marked \cup {v}
    /\ frontier' = frontier \ {v}
    /\ pc' = IF frontier = {} THEN "done" ELSE "exploring"

Done ==
    /\ pc = "done"
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc>>

InitStep == \E n \in Nodes : Explore(n)
MarkStep == \E v \in Nodes : Mark(v)

Next == InitStep \/ MarkStep \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A u \in Nodes : u \in marked => (Successors(u) \subseteq marked \cup frontier)

Invariant2 ==
    reachableFrom(marked) \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

Invariant3 ==
    reachableFrom(Root) = marked \cup reachableFrom(frontier)

PartialCorrectness ==
    (pc = "done") => (marked = reachableFrom(Root))

====