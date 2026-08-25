---- MODULE ReachableProofs ----
EXTENDS Naturals, SeqReachAlg, ReachabilityLemmas

CONSTANTS
    Nodes,               \* The set of all graph nodes
    Root                 \* The distinguished start node

VARIABLES
    Marked,              \* Set of nodes that have been marked as reachable
    Frontier,            \* Set of nodes on the current frontier
    pc                   \* Program counter of the sequential algorithm

\* ----------------------------------------------------------------------
\* State predicates from the underlying algorithm module
\* (These are assumed to be defined in SeqReachAlg)
\* ----------------------------------------------------------------------
Init == InitAlg
Next == NextAlg

\* ----------------------------------------------------------------------
\* Auxiliary definitions (assumed to be provided by ReachabilityLemmas)
\*   Succ[n]    – the set of immediate successors of node n
\*   Reachable(S) – the set of nodes reachable from any node in set S
\* ----------------------------------------------------------------------
\* (No additional definitions are required here; they are imported.)

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
TypeCorrectness ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"init","step","done"}

SuccessorCondition ==
    \A n \in Marked : Succ[n] \subseteq Marked \cup Frontier

Inv1 == TypeCorrectness /\ SuccessorCondition

\* ----------------------------------------------------------------------
\* Invariant 2: relationship between marked, frontier and reachability
\* ----------------------------------------------------------------------
Inv2 == (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals reachable set from the root at termination
\* ----------------------------------------------------------------------
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

\* ----------------------------------------------------------------------
\* Collection of all invariants required by the specification
\* ----------------------------------------------------------------------
INVARIANTS == {Inv1, Inv2, Inv3}

\* ----------------------------------------------------------------------
\* Additional safety properties (none beyond the invariants in this model)
\* ----------------------------------------------------------------------
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* The complete specification of the system
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

====