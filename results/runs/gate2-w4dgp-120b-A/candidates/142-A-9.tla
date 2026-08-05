---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachableProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

ReachableAll == Reachable(Root)
MarkedFrontier == marked \cup frontier

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {0, 1, 2}

Reach == {n \in Nodes : \E m \in marked : n \in SuccSat(m)}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ(Root)
    /\ pc = 0

\* Explore one frontier node's successors into the frontier.
ExploreFrontier ==
    /\ pc = 0
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ n \notin marked
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \cup Succ(n)) \ {n}
    /\ pc' = 1

\* When every reachable node is already marked, the frontier becomes empty.
TouchDown ==
    /\ pc = 0
    /\ frontier \subseteq Reach
    /\ frontier' = {}
    /\ pc' = 2

Done == pc = 2 /\ frontier = {}

Next == ExploreFrontier \/ TouchDown \/ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

\* Induction: marked stays type-correct and no reachable node is lost.
TypePreserved ==
    /\ TypeOK
    /\ \A m \in marked : Succ(m) \subseteq MarkedFrontier

\* Lemma 1: adding the frontier gives exactly the reachable nodes.
FrontierComplete == ReachableAll = Reachable(MarkedFrontier)

\* Lemma 2: adding successors never shrinks reachability.
ReachableFrontier ==
    ReachableAll = marked \cup Reachable(frontier)

TouchDownComplete == frontier = {} => marked = ReachableAll

====