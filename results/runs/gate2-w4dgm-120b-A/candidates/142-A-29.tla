---- MODULE ReachableProofs ----
EXTENDS Reachability, ReachableAlgorithms

CONSTANTS Nodes, Root

Spec == Init /\ [][Next]_vars
Init == ReachableAlgorithms!Init
Next == ReachableAlgorithms!Next

INVARIANT TypeOK
INVARIANT MarkingCoherent
INVARIANT FrontierReachesAll

ReachableSetEqualsMarked == ReachableSetEqualsMarked
====