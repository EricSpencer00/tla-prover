---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1, 2}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

Explore ==
    /\ pc = 0
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup {n}
    /\ pc' = 1

Advance ==
    /\ pc \in {0, 1}
    /\ frontier # {}
    /\ pc' = IF pc = 0 THEN 1 ELSE 2
    /\ UNCHANGED <<marked, frontier>>

Quiesce ==
    /\ pc = 2
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ Explore
    \/ Advance
    \/ Quiesce

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Invariant1 ==
    /\ TypeOK
    /\ \A s \in marked, t \in Nodes :
         (s \in marked /\ t \in frontier) => (t \in marked \/ t \in frontier)

Invariant2 ==
    marked \cup {v \in Nodes : \E m \in frontier : \E p \in Nodes^* :
        /\ p[1] = Root
        /\ p[Len(p)] = m
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i + 1]>> \in frontier
        /\ v = p[Len(p)]} =
    {v \in Nodes : \E m \in (marked \cup frontier) : \E p \in Nodes^* :
        /\ p[1] = Root
        /\ p[Len(p)] = m
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i + 1]>> \in (marked \cup frontier)
        /\ v = p[Len(p)]}

Invariant3 ==
    {v \in Nodes : \E p \in Nodes^* :
        /\ p[1] = Root
        /\ p[Len(p)] = v
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i + 1]>> \in frontier} =
    {v \in Nodes : \E p \in Nodes^* :
        /\ p[1] = Root
        /\ p[Len(p)] = v
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i + 1]>> \in marked}

PartialCorrectness ==
    /\ pc = 2
    /\ frontier = {}
    /\ {v \in Nodes : \E p \in Nodes^* :
          /\ p[1] = Root
          /\ p[Len(p)] = v
          /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i + 1]>> \in Nodes} = marked

INVARIANTS == {Invariant1, Invariant2, Invariant3}
PROPERTIES == {PartialCorrectness}
====