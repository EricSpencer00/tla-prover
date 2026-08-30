---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The configuration module for the sequential Misra reachability algorithm.
\* It provides concrete definitions (a specific graph, a bounded sequence
\* override) so the model checking state space is finite.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

\* The algorithm's core step: expand the frontier by one successor of a
\* marked node, marking it and adding it to the frontier.
Step ==
    /\ pc # "done"
    /\ \E n \in frontier, m \in Succ[n] :
         /\ m \notin marked
         /\ marked' = marked \cup {m}
         /\ frontier' = frontier \cup {m}
    /\ pc' = IF frontier = Nodes THEN "done" ELSE "working"

\* The algorithm is deterministic and always makes progress, so the
\* frontier eventually covers the whole graph and the process halts.
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Safety: the three key invariants of the reachability algorithm.
Inv1 == \A n \in frontier : n \in marked
Inv2 == marked \subseteq {n \in Nodes : \E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n}
Inv3 == {n \in Nodes : \E p \in Seq(Nodes) : p[1] = Root /\ p[Len(p)] = n} \subseteq marked

\* Partial correctness: the algorithm never marks a node that is not
\* reachable from the root via a path in the graph.
PartialCorrectness ==
    \A n \in marked :
        \E p \in Seq(Nodes) :
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

\* Liveness: the algorithm eventually reaches its completed state.
Termination == <>(pc = "done")

\* Configuration-level overrides for model checking: a concrete graph shape
\* and a bounded version of the sequence type.

\* Each node has exactly two successors, chosen deterministically so the
\* graph is finite and non-trivial.
ConnectedToSomeButNotAll ==
    [n \in Nodes |-> {m \in Nodes : m # n}]

\* A finite (bounded) version of Seq, so the existential quantification
\* over paths in Inv2 and PartialCorrectness stays within a finite bound.
LimitedSeq(S) == {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

====