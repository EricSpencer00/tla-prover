---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* The model checking configuration binds the abstract Succ operator to a concrete
\* per-node successor relation where each node has exactly two successors, chosen
\* deterministically (first two nodes after it in cyclic order). This keeps the
\* search space small so TLC can finish, while still providing non-trivial
\* branching in the graph that the reachability algorithm must explore.
\* Succ is redefined (not redeclared) below per the .cfg substitution rule.
ConnectedToSomeButNotAll == Nodes \ {Root}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "running"

Next ==
    \/ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \cup Succ[n]) \ {n}
    \/ (frontier = {} /\ pc' = "done")
    \/ (pc' = "running" /\ frontier' = frontier /\ marked' = marked)

Spec == Init /\ [][Next]_vars

\* Invariant: successor closure of the marked set - no node has a successor outside it.
Inv1 == \A n \in marked : Succ[n] \subseteq marked

Inv2 == marked \cap frontier = {}

Inv3 == marked \cup frontier = Nodes

\* Partial correctness: every node is eventually marked reachable from the root.
PartialCorrectness == \A n \in Nodes : <>(n \in marked)

\* Liveness: the algorithm always eventually reaches a completed state.
Termination == <>(pc = "done")

\* Substituted by the .cfg: this bounded replacement of Seq makes existential
\* paths over the graph finite rather than open-ended, keeping the model checkable.
LimitedSeq == (x \in Seq(Nodes)) /\ Len(x) <= Cardinality(Nodes)

====