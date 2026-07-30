---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachableConfig, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE Post(_)
Post(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE z \in S : TRUE IN Reachable(x) \cup Post(S \ {x})

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "halt"}

Init ==
    /\ marked = {Root}
    /\ frontier = Reachable(Root)
    /\ pc = "working"

Expand ==
    /\ pc = "working"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \ {n}) \cup (Reachable(n) \ marked)
    /\ pc' = pc

Halt ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "halt"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Expand
    \/ Halt

Spec == Init /\ [][Next]_vars

Inductive ==
    /\ TypeOK
    /\ \A m \in marked : Reachable(m) \subseteq marked \cup frontier

ReachabilitySplit ==
    marked \cup Post(frontier) = Post(marked \cup frontier)

RootReachableSet ==
    Post({Root}) = marked \cup Post(frontier)

PartialCorrectness ==
    pc = "halt" => marked = Post({Root})

====