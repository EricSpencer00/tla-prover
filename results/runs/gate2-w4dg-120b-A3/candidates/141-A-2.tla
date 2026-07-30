---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore(n) ==
    \/ /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup (Succ[n])
       /\ pc' = pc
    \/ /\ n \in marked
       /\ frontier' = frontier \ {n}
       /\ marked' = marked
       /\ pc' = pc

Next ==
    \/ \E n \in frontier : Explore(n)
    \/ /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Inv1 ==
    \A n \in marked : \A m \in Succ[n] : m \in marked \cup frontier

Inv2 ==
    (marked \cup frontier) \cup (ReachableFromSet(frontier)) = ReachableFromSet(marked \cup frontier)

Inv3 ==
    ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)

PartialCorrectness ==
    (pc = "done") => (marked = ReachableFromSet({Root}))

Termination ==
    (FrontierFinite(frontier) /\ WF_vars(Next)) ~> (pc = "done")

FrontierFinite(f) ==
    \E k \in Nat : Cardinality(f) <= k

RECURSIVE ReachableFromSet(_)
ReachableFromSet(S) ==
    LET addFront(s) == s \cup (UNION {Succ[n] : n \in s})
    IN
        IF s = addFront(s) THEN s ELSE ReachableFromSet(addFront(s))

RECURSIVE ReachableFromNode(_)
ReachableFromNode(n) ==
    LET addFront(s) == s \cup (UNION {Succ[m] : m \in s})
    IN
        IF s = addFront(s) THEN s ELSE ReachableFromNode(addFront(s))

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq == Cardinality(TABLE \X \{1}) \/ Cardinality(TABLE \X \{2}) \/ Cardinality(TABLE \X \{3})
====