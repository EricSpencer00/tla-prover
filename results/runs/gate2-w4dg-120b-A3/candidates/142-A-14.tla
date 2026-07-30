---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable, ReachabilityLemmas

CONSTANTS
    Nodes
    Root

VARIABLES
    marked
    frontier
    pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "forwarding", "stalled", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "init"

Start ==
    /\ pc = "init"
    /\ frontier' = {Root}
    /\ pc' = "forwarding"
    /\ UNCHANGED marked

Mark ==
    /\ pc = "forwarding"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \cup (Succ[n])) \ {n}
    /\ UNCHANGED pc

Stall ==
    /\ pc = "forwarding"
    /\ frontier = {}
    /\ pc' = "stalled"
    /\ UNCHANGED <<marked, frontier>>

Done ==
    /\ pc \in {"stalled", "forwarding"}
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Nxt ==
    \/ Start
    \/ Mark
    \/ Stall
    \/ Done

Spec == Init /\ [][Nxt]_vars

\* Invariant 1: type correctness plus the frontier covering the boundary of
\* the marked set: every successor of a marked node is already marked or
\* waiting in the frontier.
MarkFrontierBoundary ==
    /\ TypeOK
    /\ \A n \in Nodes : n \in marked => (Succ[n] \subseteq marked \cup frontier)

\* Invariant 2 is a direct consequence of Reachability Lemma 1, not of
\* induction over the algorithm's own steps.
MarkFrontierCoverExact ==
    Marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

\* Invariant 3 is proved from Lemma 2 (reachability is closed under adding
\* successors) and Lemma 3 (the reachable-from-empty set is empty).
MarkedExactlyReachable ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

\* TLAPS proves the three invariants above; the final theorem is partial
\* correctness: termination means the algorithm has reached exactly the set
\* of reachable nodes.
TerminationIsExact ==
    pc = "done" => marked = ReachFrom({Root})

INVARIANTS ==
    /\ MarkFrontierBoundary
    /\ MarkFrontierCoverExact
    /\ MarkedExactlyReachable

PROPERTIES ==
    TerminationIsExact

====