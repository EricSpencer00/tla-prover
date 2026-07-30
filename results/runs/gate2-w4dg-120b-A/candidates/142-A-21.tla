---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

InitState ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = 0

Expand ==
    /\ pc = 0
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = 1

Exploit(N) ==
    /\ pc = 1
    /\ N \in marked
    /\ \E S \in frontier : \A y \in S : y \notin marked /\ \A z \in marked : y # z
    /\ frontier' = frontier \cup {S}
    /\ pc' = 1
    /\ UNCHANGED marked

Terminate ==
    /\ pc = 1
    /\ frontier = {}
    /\ pc' = 2
    /\ UNCHANGED <<marked, frontier>>

Spec == InitState /\ [][Expand \/ Terminate]_vars /\ \A N \in Nodes : [Exploit(N)]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq SUBSET Nodes
    /\ pc \in 0..2

SuccessorsOf(S) == {y \in Nodes : \E x \in S : y \in S}

Invariant1 ==
    /\ TypeOK
    /\ \A S \in frontier : SuccessorsOf(S) \subseteq marked \cup S

\* Lemma 1: Reachability distributes across successor expansion.
Invariant2 ==
    Reachable(marked) \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Lemma 2: Reachable-from is stable under adding successors of a set.
\* Lemma 3: Reachable-from the empty set is empty.
Invariant3 ==
    Reachable(Root) = marked \cup Reachable(frontier)

\* Partial correctness: on termination the marked set is the reachable set.
PartialCorrectness == pc = 2 => marked = Reachable(Root)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====