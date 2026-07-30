---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, Misra

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {0, 1, 2}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

StartExplore ==
    /\ pc = 0
    /\ frontier = {}
    /\ frontier' = Succ(Root)
    /\ pc' = 1
    /\ UNCHANGED marked

Explore ==
    /\ pc = 1
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = Succ(frontier)
    /\ UNCHANGED pc

Finish ==
    /\ pc = 1
    /\ frontier = {}
    /\ pc' = 2
    /\ UNCHANGED <<marked, frontier>>

Next == StartExplore \/ Explore \/ Finish

Spec == Init /\ [][Next]_vars

\* Invariant 1: type, plus every successor of a marked node is already
\* known (marked or in the frontier).
Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ({n}) \subseteq (marked \cup frontier)

\* Invariant 2: the marked set plus what is reachable from the frontier is
\* exactly what is reachable from the combined marked/frontier set (proved
\* from Lemma 1 of the reachability-lemmas module).
Invariant2 ==
    (marked \cup Reachable(frontier)) = Reachable(marked \cup frontier)

\* Invariant 3: the nodes reachable from the root are precisely the marked
\* set plus the nodes reachable from the frontier (proved from Lemma 2 and
\* Lemma 3 of the reachability-lemmas module).
Invariant3 ==
    Reachable(Root) = (marked \cup Reachable(frontier))

PartialCorrectness ==
    (pc = 2) ~> (marked = Reachable(Root))

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness

====