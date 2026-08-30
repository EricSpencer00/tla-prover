---- MODULE ReachableProofs ----
EXTENDS SequentialMISRAlgorithm, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == /\ marked = {Root}
        /\ frontier = {}
        /\ pc = "searching"

Mark(n) == /\ pc = "searching"
           /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup {n}
           /\ pc' = "searching"

Explore(n) == /\ pc = "searching"
              /\ n \in frontier
              /\ frontier' = frontier \ {n}
              /\ pc' = "searching"
              /\ UNCHANGED marked

Terminate == /\ pc = "searching"
             /\ frontier = {}
             /\ pc' = "done"
             /\ UNCHANGED <<marked, frontier>>

Idle == /\ pc = "done"
        /\ UNCHANGED vars

Next == Mark("n1") \/ Mark("n2") \/ Explore("n1") \/ Explore("n2")
        \/ Terminate \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"searching", "done"}
          /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

FrontierClosure == \A n \in marked : Succ(n) \subseteq (marked \cup frontier)
FrontierInvariance == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)
ReachableClosure == ReachableFromRoot = marked \cup Reachable(frontier)

TerminationSafe == (pc = "done") => (marked = ReachableFromRoot)

====