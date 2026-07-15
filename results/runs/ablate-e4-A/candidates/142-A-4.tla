---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, TLC

EXTENDS ReachabilityAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

Inv1 == TypeOK /\ \A v \in Marked : \A s \in Succs[v] : s \in Marked \/ s \in Frontier

Inv2 == Marked \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

====