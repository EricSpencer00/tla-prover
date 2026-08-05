---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's reachable-set algorithm: a BFS variant whose marked and frontier
\* sets may overlap, an invariant that simplifies parallelization.
\* The .cfg swaps in a bounded Succ and a finite Seq (via LimitedSeq) for
\* model checking, so the module declares only the names it implements.

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "loop", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

\* Pick a frontier node and add its successors (overlap permitted), or
\* remove an already-marked node -- the overlap is the whole point.
Explore(n) ==
    /\ pc = "loop"
    /\ n \in frontier
    /\ IF n \in marked
       THEN /\ frontier' = frontier \ {n}
            /\ UNCHANGED marked
       ELSE /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ(n)
    /\ UNCHANGED pc

StartLoop ==
    /\ pc = "start"
    /\ pc' = "loop"
    /\ UNCHANGED <<marked, frontier>>

Terminate ==
    /\ pc = "loop"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ StartLoop
    \/ \E n \in Nodes: Explore(n)
    \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* Frontier overlap: every reachable node is either marked already or
\* reachable from the frontier, so no reachable node is ever dropped.
Inv1 == \A n \in marked : \A m \in Succ(n) : m \in marked \cup frontier

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

PartialCorrectness ==
    frontier = {} => ReachableFrom({Root}) = marked

\* The algorithm makes progress as long as it can: either by marking a new
\* node (enlarging the finite reachable set) or by shrinking the frontier.
Progress ==
    \/ \E n \in frontier : n \in marked /\ frontier' = frontier \ {n}
    \/ \E n \in frontier : n \notin marked /\ marked' = marked \cup {n}

Termination == (pc = "loop") ~> (pc = "done") /\ WF_vars(Progress)

====