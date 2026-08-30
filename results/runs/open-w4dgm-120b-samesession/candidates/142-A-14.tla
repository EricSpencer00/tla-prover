---- MODULE ReachableProofs ----
EXTENDS Numeral, Reachable, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

\* Re-entrant dispatch: always available, resetting the frontier and marked
\* set to start a fresh reachability sweep from the root.
Dispatch ==
    /\ pc' = "active"
    /\ marked' = {Root}
    /\ frontier' = {Root}
    /\ UNCHANGED <<>>

\* A frontier node may be marked, and its successors added to the frontier;
\* the frontier strictly shrinks, so this is never stuck.
Explore(n) ==
    /\ pc = "active"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \cup Reachable.Succ(n)) \ {n}
    /\ UNCHANGED <<pc>>

Done ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Dispatch
    \/ \E n \in Nodes: Explore(n)
    \/ Done

Spec == Init /\ [][Next]_vars

\* The three invariants below are proved, not checked. The first is
\* inductive type-and-successor correctness; the second is Lemma 1; the third
\* combines Lemma 2 (reachable-from is stable under Adding successors)
\* with Lemma 3 (reachable-from empty is empty).
Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : Reachable.Succ(n) \subseteq marked \cup frontier

Invariant2 ==
    Reachable.From(marked) \cup Reachable.From(frontier) = Reachable.From(marked \cup frontier)

Invariant3 ==
    Reachable.From({Root}) = marked \cup Reachable.From(frontier)

\* No liveness property here: TLAPS does not yet support liveness reasoning.
PartialResult ==
    (pc = "done") => (marked = Reachable.From({Root}))

INVARIANT Invariant1
INVARIANT Invariant2
INVARIANT Invariant3
PROPERTY PartialResult

====