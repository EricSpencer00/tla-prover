---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's BFS variant: the frontier and the marked set may overlap, so the loop
\* never removes a node from the frontier when it is first marked.
Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ IF n \notin marked
           THEN /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
           ELSE /\ frontier' = frontier \ {n}
                /\ marked' = marked
    /\ pc' = "running"

Done ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars

\* Safety: the frontier is always the part of the reachable set that has not
\* been marked yet, so no node reachable from the root is ever lost.
Inv1 ==
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier
    /\ (marked \cup frontier) \cup Succ[frontier] = Succ[marked \cup frontier]
    /\ Reachable(Root) = marked \cup Succ[frontier]

\* Reachable is the standard graph-reachability operator over the (possibly
\* infinite) Succ relation, defined without explicit recursion so it works on
\* infinite graphs too.
Reachable(n) ==
    LET F[S \in SUBSET Nodes] ==
        S \cup {n \in Nodes : \E p \in S : n \in Succ[p]}
    IN F^{\omega}({n})

PartialCorrectness == pc = "done" => Reachable(Root) = marked

Termination == \A n \in Nodes : Reachable(n) => <>(n \in marked)

\* Invariant with infinite reachability: the frontier never stays non-empty
\* forever when the reachable part is finite.
Fair == \A n \in Nodes : (n \in marked) ~> (n \in frontier)

====