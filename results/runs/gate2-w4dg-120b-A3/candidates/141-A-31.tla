---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* "ConnectedToSomeButNotAll" is the name the .cfg substitutes in for Succ, so
\* "Succ" above is never used in the model but must still be declared.
ConnectedToSomeButNotAll == ConnectedToSomeButAll

\* LimitedSeq replaces the unbounded Seq operator from Sequences with a finite
\* version, as the .cfg substitutes it for Seq; the extension stays in place.
LimitedSeq == Seq

VARIABLES visited, frontier, pc
vars == << visited, frontier, pc >>

TypeOK ==
    /\ visited \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ visited = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The frontier need not be disjoint from visited; that is the whole point of
\* Misra's overlapping variant.
MarkStep ==
    \/ \E n \in frontier :
        /\ n \notin visited
        /\ visited' = visited \cup {n}
        /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
        /\ UNCHANGED pc
    \/ \E n \in frontier :
        /\ n \in visited
        /\ frontier' = frontier \ {n}
        /\ UNCHANGED << visited, pc >>

Terminate == frontier = {} /\ pc' = "done" /\ UNCHANGED << visited, frontier >>

Next == MarkStep \/ Terminate

Spec == Init /\ [][Next]_vars
    /\ WF_vars(MarkStep)

\* The reachable relation is defined for the whole graph, not just the current
\* explored component.
ReachableFrom(n) ==
    LET Recur(m) == IF m = n THEN {n} ELSE {m} \cup (UNION {Recur(k) : k \in ConnectedToSomeButNotAll[m]})
    IN UNION {Recur(k) : k \in Nodes}

Inv1 ==
    \A n \in visited : ConnectedToSomeButNotAll[n] \subseteq (visited \cup frontier)

Inv2 ==
    \A n \in frontier : ReachableFrom(n) \subseteq ReachableFrom(visited \cup frontier)

Inv3 ==
    ReachableFrom(Root) = (visited \cup ReachableFrom(frontier))

PartialCorrectness ==
    (pc = "done") => (visited = ReachableFrom(Root))

Termination == (Cardinality(ReachableFrom(Root)) < \infty) ~> (pc = "done")
====