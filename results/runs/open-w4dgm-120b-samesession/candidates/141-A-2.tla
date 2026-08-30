---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "term"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* Misra's variant: the frontier may retain already-marked nodes so that
\* parallel workers can keep picking from it without coordination.
Explore(n) ==
    \/ n \in frontier /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
    \/ n \in frontier /\ n \in marked
        /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {n} THEN "term" ELSE pc

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

\* The "frontier" is not a cut: it may overlap with the visited set. What must
\* hold is that no reachable node is ever stranded outside both.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

ReachableFrom(S) ==
    LET f[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE LET x == CHOOSE y \in T : TRUE IN Succ[x] \cup f[T \ {x}]
    IN f[S]

\* A node reachable from the union of visited-and-frontier is reachable from
\* either component, which is exactly what rules out a lost reachable node.
Inv2 ==
    ReachableFrom(marked \cup frontier) \subseteq
        (ReachableFrom(marked) \cup ReachableFrom(frontier))

Inv3 ==
    ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness ==
    /\ ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)
    /\ ReachableFrom(frontier) \subseteq ReachableFrom(marked)

\* Termination is only guaranteed when the reachable set is finite; the
\* fairness of the frontier pick is what forces progress.
Termination ==
    \A s \in SUBSET Nodes : (ReachableFrom({Root}) = s /\ s # {})
        => (pc ~> (pc = "term"))

\* The cfg substitutes a bounded version of Succ into this operator.
ConnectedToSomeButNotAll == UNCHANGED <<marked, frontier, pc>>

\* The cfg substitutes this finite-version operator over Seq from Sequences.
LimitedSeq == UNCHANGED <<marked, frontier, pc>>
====