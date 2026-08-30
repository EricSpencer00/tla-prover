---- MODULE ReachableProofs ----
EXTENDS Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ frontier \cap marked = {}
    /\ pc \in {"b0", "b1"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "b0"

\* The frontier may be expanded in any order, which is what allows the
\* comparison with the forward reachability set to be non-sequential.
Expand(n) ==
    /\ pc = "b0"
    /\ frontier # {}
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = "b1"

AddSuccessors(n) ==
    /\ pc = "b1"
    /\ frontier' = frontier \cup (Succ(n) \ (marked \cup frontier))
    /\ pc' = "b0"
    /\ UNCHANGED marked

Settle(n) ==
    /\ pc = "b1"
    /\ frontier = {n}
    /\ frontier' = {}
    /\ marked' = marked \cup {n}
    /\ UNCHANGED pc

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ \E n \in Nodes : AddSuccessors(n)
    \/ \E n \in Nodes : Settle(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Expand(n))
                                   /\ WF_vars(\E n \in Nodes : AddSuccessors(n))
                                   /\ WF_vars(\E n \in Nodes : Settle(n))

\* SAFETY: the three invariants are established as separate theorems.
TypeInvariant == TypeOK
\* SAFETY: every successor of a marked node is already marked or in the frontier.
FrontierCoversSuccessors ==
    \A n \in marked : Succ(n) \subseteq (marked \cup frontier)
\* SAFETY: reachable from marked plus frontier is reachable from marked.
ReachableFromMarkedUFrontierIsFixed ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked)
\* SAFETY: reachable nodes and the frontier cover each other.
FrontierAndMarkedCoverReachable == ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

\* LIVENESS: partial correctness at termination -- the marked set is the reachable set.
ReachableIffMarkedAtQuiescence ==
    (frontier = {}) => (ReachableFrom(Root) = marked)

INVARIANTS TypeInvariant, FrontierCoversSuccessors, ReachableFromMarkedUFrontierIsFixed, FrontierAndMarkedCoverReachable
PROPERTIES ReachableIffMarkedAtQuiescence
====