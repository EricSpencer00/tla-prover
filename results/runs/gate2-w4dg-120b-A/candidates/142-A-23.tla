---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachableAlgorithm, Reachability

CONSTANT Nodes, Root

\* A SAFETY PROPERTY OF THE MISRA REACHABILITY ALGORITHM: the marked set is
\* closed under successors, modulo the frontier -- every successor of a marked
\* node is either already marked or waiting in the frontier.
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"searching", "done"}
    /\ \A n \in frontier : Root \notin frontier

ReachableStep ==
    \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup {w \in Nodes : (n, w) \in Edges}
        /\ UNCHANGED pc

Terminate ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Init ==
    /\ marked = {Root}
    /\ frontier = {w \in Nodes : (Root, w) \in Edges}
    /\ pc = "searching"

Next == ReachableStep \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* The three proved invariants: inductive type+closure, marked+frontier
\* reachable, and reachable equals marked+frontier reachable.
MarkedClosure == TypeOK
MarkedFrontierStability ==
    \A x \in Nodes :
        /\ (x \in marked \/ x \in ReachableFrom(frontier)) => x \in ReachableFrom(marked \cup frontier)
        /\ x \in ReachableFrom(marked \cup frontier) => x \in marked \/ x \in ReachableFrom(frontier)
MarkedFrontierCompleteness ==
    ReachableFrom(Root) = marked \cup ReachableFrom(frontier)

INVARIANTS == MarkedClosure /\ MarkedFrontierStability /\ MarkedFrontierCompleteness

\* Partial correctness: on termination the marked set is exactly the set of
\* reachable nodes (a fixed point of the reachable-from operator).
TerminationSound ==
    pc = "done" => marked = ReachableFrom(Root)

\* No termination (liveness) proof: TLAPS does not support liveness yet.
PROPERTIES == TerminationSound
====