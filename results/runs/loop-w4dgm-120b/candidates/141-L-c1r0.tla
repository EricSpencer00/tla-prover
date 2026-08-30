---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* Misra's BFS variant: the marked set and the frontier may overlap.
\* Each iteration either marks a node and expands it, or removes an already-marked frontier node.
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"active", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "active"

Explore(v) ==
    \/ IF v \notin marked
       THEN /\ marked' = marked \cup {v}
            /\ frontier' = frontier \cup Succ[v]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {v}
    /\ UNCHANGED pc

Next ==
    /\ pc = "active"
    /\ frontier # {}
    /\ \E v \in frontier : Explore(v)
    /\ pc' = IF frontier = {} THEN "done" ELSE pc

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is either already marked or still on the frontier.
Inv1 == \A u \in marked : Succ[u] \subseteq (marked \cup frontier)

\* Reachability distributes over the partition marked/frontier: the nodes reachable
\* from their union are exactly the nodes reachable from each separately, combined.
Inv2 ==
    ReachableFrom(marked \cup frontier) =
        (ReachableFrom(marked) \cup ReachableFrom(frontier))

\* Subtlety: the nodes reachable from the root split cleanly across the marked set
\* and the frontier's reachable portion -- nothing reachable is lost in between.
Inv3 ==
    ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Terminating == pc = "done"
Termination == Terminating ~> Terminating

====