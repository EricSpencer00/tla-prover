---- MODULE ReachableProofs ----
EXTENDS SeqReachabilityAlgo, GraphLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

Init == SeqReachabilityAlgo.Init
Next == SeqReachabilityAlgo.Next
Spec == Init /\ [][Next]_ <<marked, frontier, pc>>

TypeOK == marked \subseteq Nodes /\ frontier \subseteq Nodes

SuccessorInMarkedOrFrontier ==
    \A n \in marked : Adj[n] \subseteq marked \/ frontier

Invariant1 == TypeOK /\ SuccessorInMarkedOrFrontier
Invariant2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)
Invariant3 == Reachable({Root}) = marked \cup Reachable(frontier)

CorrectOnTermination == pc = "Done" => marked = Reachable({Root})

THEOREM CorrectOnTermination == pc = "Done" => marked = Reachable({Root})

====