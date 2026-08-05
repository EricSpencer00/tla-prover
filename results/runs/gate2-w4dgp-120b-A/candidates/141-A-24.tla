---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

\* Misra's algorithm: with the frontier overlapping the visited set, marking a
\* node may redundantly re-queue it, so picking it again simply removes it.
ExploreStep ==
    /\ frontier # {}
    /\ \E u \in frontier :
        \/ /\ u \notin marked
            /\ marked' = marked \cup {u}
            /\ frontier' = frontier \cup Succ[u]
         \/ /\ u \in marked
            /\ frontier' = frontier \ {u}
            /\ marked' = marked
    /\ pc' = "idle"

Terminate ==
    /\ frontier = {}
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Next == ExploreStep \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"idle"}

\* While the algorithm is running the frontier and visited sets guard each
\* other: a successor of a visited node is either already visited or waiting
\* in the frontier, so nothing reachable is left outside both.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup frontier) = (ReachableFrom(Nodes, UnionPairs) \cup frontier)
    where
        UnionPairs == marked \cup frontier
        ReachableFrom(V, pairs) ==
            LET R == {x \in V : \E y \in V : <<y, x>> \in pairs}
            IN IF R = {} THEN {} ELSE R \cup ReachableFrom(R, pairs)

Inv3 == ReachableFrom(Nodes, {{n, m} : n \in Nodes, m \in Succ[n]})
          = (marked \cup ReachableFrom(Nodes, {{n, m} : n \in frontier, m \in Succ[n]}})

PartialCorrectness == (frontier = {}) => (ReachableFrom(Nodes, {{n, m} : n \in Nodes, m \in Succ[n]}} = marked)

Termination == (ReachableFrom(Nodes, {{n, m} : n \in Nodes, m \in Succ[n]}} # {}) ~> (frontier = {})

\* Operators substituted by the .cfg -- the names on the left are overridden.

ConnectedToSomeButNotAll == {1, 2, 4}

LimitedSeq == Seq

====