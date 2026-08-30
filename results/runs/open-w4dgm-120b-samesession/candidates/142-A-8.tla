---- MODULE ReachableProofs ----
EXTENDS MisraSeq, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Search == /\ frontier # {}
          /\ pc = "idle"
          /\ pc' = "searching"
          /\ UNCHANGED << marked, frontier >>

Expand(n) == /\ pc = "searching"
             /\ n \in frontier
             /\ frontier' = frontier \ {n}
             /\ marked' = marked \cup {n}
             /\ pc' = IF frontier = {n} THEN "done" ELSE pc

Idle == /\ pc = "idle"
        /\ frontier = {}
        /\ UNCHANGED vars

Done == /\ pc = "done"
        /\ UNCHANGED vars

Next ==
    \/ Search
    \/ \E n \in Nodes : Expand(n)
    \/ Idle
    \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == (marked \cup frontier) \cup Succ(marked \cup frontier)
                  = reachableFrom(marked \cup frontier)

Invariant3 == reachableFrom(Root) = (marked \cup frontier) \cup reachableFrom(frontier)

TerminationSafe ==
    (pc = "done" /\ frontier = {}) => reachableFrom(Root) = marked

====