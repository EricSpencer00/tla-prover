---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ

TypeOK ==
    /\ Nodes \subseteq Nat
    /\ Succ \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : Cardinality(Succ[n]) = 2

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* Reachability needs existential paths; the cfg forces Succ to a bounded
\* version of the graph, and Seq to a FINITE version, so existential
\* quantification over paths stays finite and model-checkable.
Reachable(n) ==
    \E seq \in [1..Cardinality(Nodes) -> Nodes] :
        \A i \in 1..(Cardinality(Nodes) - 1) :
            seq[i + 1] \in Succ[seq[i]]
        /\ seq[1] = Root
        /\ seq[Cardinality(Nodes)] = n

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "running"
    /\ TypeOK

Expand(n) ==
    /\ n \in frontier
    /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ marked' = marked \cup Succ[n]
    /\ UNCHANGED pc

Idle ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ Idle

Spec == Init /\ [][Next]_vars

\* Successor closure: frontier is fully absorbed into marked once the run stops.
Inv1 == frontier \subseteq marked

\* Reachable nodes, under the bounded Succ graph, stay inside the marked set.
Inv2 == {n \in Nodes : Reachable(n)} \subseteq marked

\* Every marked node is reachable from the root in the bounded graph.
Inv3 == marked \subseteq {n \in Nodes : Reachable(n)}

PartialCorrectness == marked = {n \in Nodes : Reachable(n)}

Termination == <>(pc = "done")

====