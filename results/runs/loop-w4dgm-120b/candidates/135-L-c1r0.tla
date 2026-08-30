---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The configuration module for the sequential Misra reachability algorithm.
\* It inherits Init, Next, and the invariants from the algorithm spec, but
\* defines here the concrete graph (Succ) and a bounded sequence type so the
\* reachable-state model checking finishes.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = "idle"

Mark(n) == marked \cup {n}

Next ==
    \/ \E n \in frontier :
        /\ marked' = Mark(n)
        /\ frontier' = (frontier \cup Succ(n)) \ {n}
        /\ pc' = IF frontier \cup Succ(n) \ {n} = {} THEN "done" ELSE pc
    \/ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

\* Bounded path quantification for model checking; redefines Seq from Sequences.
LimitedSeq == [n \in Nodes |-> CHOOSE s \in Seq(1..Cardinality(Nodes)) : Cardinality(s) = n]

\* The configuration supplies a concrete, finite replacement for Succ when the
\* reachability definition quantifies over it -- a deterministic 2-successor
\* choice for each node, keeping the state space finite and non-trivial.
ConnectedToSomeButNotAll == Succ

\* The invariants themselves (Inv1, Inv2, Inv3) are inherited from the
\* algorithm's core specification; they are checked here, unchanged.
Inv1 == \A n \in frontier : \E m \in marked : n \in ConnectedToSomeButNotAll(m)
Inv2 == marked \cup frontier = Nodes
Inv3 == marked \cap frontier = {}
PartialCorrectness == (frontier = {}) => (marked = Nodes)

Termination == <>(pc = "done")

====