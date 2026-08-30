---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachableBase, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "terminated"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

Reachable(S) == UNION {Reachable(n) : n \in S}

InductiveStep ==
    /\ pc = "idle"
    /\ \E n \in Nodes :
         /\ n \in marked
         /\ n \notin frontier
         /\ frontier' = frontier \cup {n}
    /\ pc' = "searching"
    /\ UNCHANGED marked

MarkSuccessor ==
    /\ pc = "searching"
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {} THEN "idle" ELSE pc

Terminate ==
    /\ pc = "idle"
    /\ frontier = {}
    /\ pc' = "terminated"
    /\ UNCHANGED <<marked, frontier>>

Next == InductiveStep \/ MarkSuccessor \/ Terminate

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus closure of marked under successors.
ReachableClosure ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Invariant 2: reachable-from marked plus frontier is the reachable set.
CombinedReachability == Reachable(marked \cup frontier) = Reachable(Nodes)

\* Invariant 3: reachable-from the root equals marked plus reachable-from frontier.
RootReachability == Reachable({Root}) = (marked \cup Reachable(frontier))

INVARIANT ReachableClosure
INVARIANT CombinedReachability
INVARIANT RootReachability

\* Partial correctness: on termination the marked set is exactly the reachable set.
TerminationMatchesReachability ==
    (pc = "terminated") => (marked = Reachable({Root}))

====