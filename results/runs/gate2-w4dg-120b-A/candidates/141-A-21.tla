---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE
             Rest == ReachableFrom(S \ {x})
         IN {x} \cup Rest \cup Succ[x]

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore(y) ==
    /\ y \in frontier
    /\ marked' = marked \cup {y}
    /\ frontier' = frontier \cup Succ[y]
    /\ pc' = pc

DropFrontier(y) ==
    /\ y \in frontier
    /\ y \in marked
    /\ frontier' = frontier \ {y}
    /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E y \in Nodes : Explore(y)
    \/ \E y \in Nodes : DropFrontier(y)
    \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "terminated"}

Inv1 ==
    \A x \in marked : Succ[x] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \in ReachableFrom(ReachableFrom(marked \cup frontier))

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    (pc = "terminated") => (marked = ReachableFrom({Root}))

Termination ==
    \A N \in Nat : (Cardinality(ReachableFrom({Root})) <= N) ~> (pc = "terminated")

====