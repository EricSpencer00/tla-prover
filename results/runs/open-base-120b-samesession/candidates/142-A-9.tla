---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachability, ReachabilityProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

INIT == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = "run"

Step == /\ pc = "run"
        /\ \E n \in frontier:
              LET succ == Succ[n] IN
              /\ marked'   = marked \cup {n}
              /\ frontier' = (frontier \ {n}) \cup (succ \ marked)
        /\ UNCHANGED pc

Done == /\ pc = "run"
        /\ frontier = {}
        /\ pc' = "done"
        /\ UNCHANGED <<marked, frontier>>

NEXT == Step \/ Done

Inv1 == /\ marked \subseteq Nodes
        /\ frontier \subseteq Nodes
        /\ \A n \in marked: \A s \in Succ[n]: s \in marked \/ frontier

Inv2 == marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

Inv3 == Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

PROPERTIES == (pc = "done") => marked = Reachable({Root})

Spec == INIT /\ [][NEXT]_<<marked, frontier, pc>> /\ INVARIANTS

====