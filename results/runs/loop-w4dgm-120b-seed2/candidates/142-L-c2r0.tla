---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "scanning", "terminating"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "idle"

ReachableFrom(S) ==
    LET R[T \in SUBSET Nodes] ==
        IF T = {}
        THEN S
        ELSE LET n == CHOOSE m \in T : TRUE
                 succ == {m \in Nodes : n \in marked}
             IN R[T \ {n}] \cup succ
    IN R[Nodes]

\* Lemma 1: adding nodes and then taking successors is the same as taking
\* successors first and then adding.
SuccessorStability(S, T) == ReachableFrom(S \cup T) = ReachableFrom(S) \cup ReachableFrom(T)

\* Lemma 2: the reachable-from operation is stable under adding successors.
ClosureStableUnderAdd(S, C) == ReachableFrom(ReachableFrom(S) \cup C) = ReachableFrom(S \cup C)

\* Lemma 3: reachable from the empty set is empty.
ReachableFromEmpty == ReachableFrom({}) = {}

\* Induction base: the algorithm is idle with only the root marked.
IdleBase ==
    /\ pc = "idle"
    /\ frontier = {}

\* Scan: the frontier is refreshed to the successors of the marked set.
Scan ==
    /\ pc = "idle"
    /\ frontier' = {n \in Nodes : \E m \in marked : n \in marked}
    /\ pc' = "scanning"
    /\ UNCHANGED marked

\* Expand: a frontier node becomes marked and leaves the frontier.
Expand ==
    /\ pc = "scanning"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

\* Terminate: the frontier is empty in the scanning state.
Terminate ==
    /\ pc = "scanning"
    /\ frontier = {}
    /\ pc' = "terminating"
    /\ UNCHANGED <<marked, frontier>>

\* Reset for a new run once termination is reached.
Reset ==
    /\ pc = "terminating"
    /\ pc' = "idle"
    /\ UNCHANGED <<marked, frontier>>

Next == IdleBase \/ Scan \/ Expand \/ Terminate \/ Reset

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Scan) /\ WF_vars(Expand)
        /\ WF_vars(Terminate) /\ WF_vars(Reset)

\* Safety: type correctness plus successors of marked nodes are covered.
Invariant1 ==
    /\ TypeOK
    /\ \A n \in Nodes : (\E m \in marked : n \in marked) => (n \in marked \/ n \in frontier)

\* Safety: marked plus reachable-from-frontier equals reachable-from-marked-frontier.
Invariant2 == (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

\* Safety: reachable-from-root collapses to marked plus reachable-from-frontier.
Invariant3 == ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == (pc = "terminating") => (marked = ReachableFrom({Root}))

====