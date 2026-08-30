---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}
    /\ Root \in Nodes

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's variant: Do not remove a newly-marked node from the frontier,
\* so marked and frontier may overlap and the action stays weakly fair.
Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ frontier' = frontier \ {n}
            /\ marked' = marked
    /\ IF frontier' = {}
       THEN pc' = "done"
       ELSE pc' = "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is already marked or still to be explored.
Inv1 == \A n \in Nodes : n \in marked => Succ[n] \subseteq (marked \cup frontier)

\* Reachable from marked alone plus frontier alone is unchanged under union.
Inv2 ==
    \A S \in {marked, frontier} :
        ReachableFromSet(S) \cup S = ReachableFromSet(S \cup frontier)

\* Reachable from the root is exactly what is marked plus what frontier can reach.
Inv3 == ReachableFromSet({Root}) = marked \cup ReachableFromSet(frontier)

PartialCorrectness == ReachableFromSet({Root}) = marked

Termination == <>(pc = "done")

\* Operators injected from the .cfg, each overriding a name from an import.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

ReachableFromSet(S) ==
    LET step[T \in SUBSET Nodes] ==
            T \cup UNION {Succ[n] : n \in T}
    IN
    IF S = {}
    THEN {}
    ELSE CHOOSE M \in {LimitedSeq(step, S)} : TRUE

\* Choose a maximal set under repeated frontier expansion; LimitedSeq(,) is
\* a bounded-width variant of the usual Seq(,) to keep the reachable closure
\* construction finite and checkable even for infinite graphs.
LimitedSeq(f, S) ==
    LET g[T \in SUBSET Nodes] == f[T]
    IN CHOOSE M \in {M \in SUBSET Nodes : M = g[M] /\ S \subseteq M} : TRUE

====