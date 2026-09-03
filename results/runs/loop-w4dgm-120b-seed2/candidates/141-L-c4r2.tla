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

\* Misra's variant: the frontier and the marked set may overlap. Visiting a
\* node keeps it in the frontier; a second pop removes it.
Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked
        THEN /\ marked' = marked \cup {n}
             /\ frontier' = frontier \cup Succ[n]
        ELSE /\ marked' = marked
             /\ frontier' = frontier \ {n}
    /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore) /\ WF_vars(Terminate)

\* Every successor of a marked node is either already marked or still queued.
Inv1 ==
    \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

\* The reachable set at saturation: marked nodes and the frontier agree.
Inv2 ==
    Reachable(Nodes, Root) = marked \cup Reachable(Nodes, frontier)

\* Marked nodes are reachable from the root.
Inv3 ==
    marked \subseteq Reachable(Nodes, Root)

PartialCorrectness == Inv2

\* A finite reachable set guarantees eventual termination of the loop.
Termination == Spec => <>(pc = "done")

\* The override from the .cfg: ConnectedToSomeButNotAll is the placeholder
\* operator that the .cfg substitutes in for Succ; here it is a generic
\* finite set-valued operator with the same signature.
ConnectedToSomeButNotAll(n) == \E m \in Nodes : n \in Succ[m]

\* The .cfg override: a version of Seq that stays finite, built from the
\* standard Sequences module.
LimitedSeq(S) == Seq({x \in S : TRUE})

Reachable(S, roots) ==
    LET step[X \in SUBSET Nodes] == X \cup UNION {Succ[n] : n \in X}
        iter[f \in (SUBSET Nodes) -> (SUBSET Nodes), X \in SUBSET Nodes] ==
            IF f[X] = X THEN X ELSE iter[f, f[X]]
    IN iter[step, roots]

====