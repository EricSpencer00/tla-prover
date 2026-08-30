---- MODULE ReachableProofs ----
EXTENDS Natural, FiniteSets, ReachableSeq, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "working"

Expand(n) ==
    /\ pc = "working"
    /\ frontier = {n}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "working"

Explore(s) ==
    /\ pc = "working"
    /\ marked # {}
    /\ frontier = {}
    /\ \E n \in marked : \E m \in Succ(n) : s = <<n, m>>
    /\ m \notin marked
    /\ frontier' = frontier \cup {m}
    /\ pc' = "working"
    /\ marked' = marked

Done ==
    /\ pc = "working"
    /\ frontier = {}
    /\ \A n \in Nodes : \A m \in Succ(n) : m \in marked
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Stalled ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ \E s \in Nodes \X Nodes : Explore(s)
    \/ Done
    \/ Stalled

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"working", "done"}
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant1 == TypeOK /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

Invariant2 == (marked \cup frontier) \cup Reach(marked \cup frontier) = Reach(Nodes)

Invariant3 == Reach(Nodes) = (marked \cup Reach(frontier))

TerminationResult ==
    /\ pc = "done"
    /\ Reach(Nodes) = marked

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == TerminationResult
====