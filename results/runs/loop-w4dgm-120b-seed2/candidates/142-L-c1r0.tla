---- MODULE ReachableProofs ----
EXTENDS Reachability, ReachableAlgo

CONSTANTS Nodes, Root

Spec == ReachableAlgo!Spec

Init == ReachableAlgo!Init

Step == ReachableAlgo!Step

Next == ReachableAlgo!Next

TypeOK == ReachableAlgo!TypeOK

Invariant1 == ReachableAlgo!Invariant1

Invariant2 == ReachableAlgo!Invariant2

Invariant3 == ReachableAlgo!Invariant3

PartialCorrectness == ReachableAlgo!PartialCorrectness

====