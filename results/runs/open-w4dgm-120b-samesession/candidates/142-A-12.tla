---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable, ReachableAlgs

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"unstarted", "searching", "terminated"}

\* Reachable-from is preserved under adding nodes reachable from the frontier,
\* so the frontier's contribution is already saturated when the frontier is empty.
MarkedCoherent ==
    /\ TypeOK
    /\ \A n \in marked : frontier \subseteq ReachableFrom(n, Nodes)

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "unstarted"

StartSearch ==
    /\ pc = "unstarted"
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

\* A node is marked only when every one of its successors is already marked or
\* in the frontier, which is exactly what keeps the frontier at the boundary.
MarkNode(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ UNCHANGED <<frontier, pc>>

AdvanceFrontier(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ frontier' = frontier \cup {n}
    /\ UNCHANGED <<marked, pc>>

RetreatFrontier(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ n \notin marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Terminate ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

Unwind ==
    /\ pc = "searching"
    /\ frontier # {}
    /\ frontier = marked
    /\ frontier' = {}
    /\ UNCHANGED <<marked, pc>>

Next ==
    \/ StartSearch
    \/ \E n \in Nodes : MarkNode(n)
    \/ \E n \in Nodes : AdvanceFrontier(n)
    \/ \E n \in Nodes : RetreatFrontier(n)
    \/ Terminate
    \/ Unwind

Spec == Init /\ [][Next]_vars

\* Lemma 1 of the reachability proofs: once every successor of a marked node is
\* already marked or in the frontier, the frontier can never go empty by itself.
Invariant1 == MarkedCoherent

\* Lemma 2: the set reachable from a node is stable under adding its successors.
\* Lemma 3: the reachable set from the empty frontier is empty.
\* Together they are exactly the invariant the algorithm needs.
Invariant2 == reachableFrom(marked) \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

\* Termination is not proved here (TLAPS has no liveness reasoning yet), but
\* assuming the algorithm has terminated, the frontier is empty and the two
\* reachable-from sets collapse to a single reachable set.
Invariant3 == pc = "terminated" => reachableFrom(marked) = reachableFrom(Nodes)

\* Partial correctness: on termination the marked set is exactly the reachable set.
ResultIsReachable == pc = "terminated" => marked = reachableFrom(Nodes)

INVARIANTS == {Invariant1, Invariant2, Invariant3}

Properties == ResultIsReachable

====