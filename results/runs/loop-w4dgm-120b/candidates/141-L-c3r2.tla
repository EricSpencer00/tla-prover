---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's variant: marking a node keeps it in the frontier; the two sets
\* may overlap, which is what makes the algorithm parallelizable.
Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ UNCHANGED pc

\* The other case of the main action: a node already marked is removed from
\* the frontier so the loop can drain.
DropStale(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Explore(n)
    \/ \E n \in Nodes : DropStale(n)
    \/ Done

Spec == Init /\ [][Next]_vars
        /\ \A x \in Nodes : SF_vars(Explore(x))
        /\ \A x \in Nodes : WF_vars(DropStale(x))

\* Reachable from a set via a (possibly infinite) forward walk of Succ.
ReachableFrom(S) ==
    LET F[T \in SUBSET Nodes] ==
        IF T = {}
        THEN {}
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == F[T \ {x}]
             IN rest \cup {x} \cup Succ[x]
    IN F[S]

\* Action closure: reachable nodes are either already marked or still
\* reachable from the frontier, so no reachable node is ever lost.
Inv1 == \A n \in Nodes : n \in marked => ReachableFrom({n}) \subseteq (marked \cup frontier)

\* Reachable via visited nodes plus reachable via the frontier covers
\* reachable via both together.
Inv2 == ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

\* Immediate consequence of Inv2: nothing reachable is missed by visited.
Inv3 == ReachableFrom({Root}) \subseteq (marked \cup ReachableFrom(frontier))

PartialCorrectness == ReachableFrom({Root}) \subseteq marked

Termination == (\A n \in Nodes : n \in frontier) ~> (frontier = {})
====