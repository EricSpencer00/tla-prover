---- MODULE ReachableProofs ----
EXTENDS SeqReach, ReachProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == {marked, frontier, pc}

Init == SeqReach.Init
Next == SeqReach.Next

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1, 2}
    /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

Invariant2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Invariant3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

Terminated == pc = 2

PartialCorrectness == Terminated => marked = Reachable({Root})

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {}

THEOREM PartialCorrectness == Terminated => marked = Reachable({Root})

====