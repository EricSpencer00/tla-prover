---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

\* Model-checking configuration for the sequential reachability algorithm.
\* The graph structure is concrete and each node has exactly two successors,
\* which bounds the state space while keeping the reachability non-trivial.
\* Sequences are bounded to length equal to the number of nodes.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

\* Reach can fire for any frontier node that is not yet marked.
Reach(n) ==
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ pc' = IF frontier \cup Succ[n] \subseteq marked \cup {n} THEN "done" ELSE pc

Next == \E n \in Nodes : Reach(n)

Spec == Init /\ [][Next]_vars

\* Every reachable node from the root is in the marked set (closure under Succ).
Inv1 == {n \in Nodes : \E s \in LimitedSeq(Nodes) : IsPath(Root, n, s)} \subseteq marked

\* Every node in the frontier is reachable from the root.
Inv2 == frontier \subseteq {n \in Nodes : \E s \in LimitedSeq(Nodes) : IsPath(Root, n, s)}

\* Every node is either marked or reachable from the root.
Inv3 == \A n \in Nodes : (n \notin marked) => \E s \in LimitedSeq(Nodes) : IsPath(Root, n, s)

PartialCorrectness == marked = {n \in Nodes : \E s \in LimitedSeq(Nodes) : IsPath(Root, n, s)}

Termination == <>(pc = "done")

====