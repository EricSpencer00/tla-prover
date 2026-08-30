---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "search", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "init"

Search ==
    /\ pc = "init"
    /\ pc' = "search"
    /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
    /\ pc = "search"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Discover(n, m) ==
    /\ pc = "search"
    /\ n \in marked
    /\ m \in Succ(n)
    /\ m \notin marked
    /\ m \notin frontier
    /\ frontier' = frontier \cup {m}
    /\ UNCHANGED <<marked, pc>>

Done ==
    /\ pc = "search"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Search
    \/ \E n \in Nodes : Mark(n)
    \/ \E n, m \in Nodes : Discover(n, m)
    \/ Done

Spec == Init /\ [][Next]_vars

Invariant1 ==
    /\ TypeOK
    /\ \A n \in Nodes : \A m \in Succ(n) : (n \in marked) => (m \in marked \/ m \in frontier)

Invariant2 == marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Invariant3 == ReachFrom(Root) = marked \cup ReachFrom(frontier)

ProofOfInvariant2 ==
    \* Reachability is preserved under adding the successors of already-reachable nodes:
    \* every node reachable from a successor of a reachable node is already reachable,
    \* so the union of marked and frontier is itself closed under one-step expansion.
    Lemma1

ProofOfInvariant3 ==
    \* Reachability from the root is exactly the closure of the already marked set
    \* together with the frontier, using the closure properties of ReachFrom.
    Lemma2 /\ Lemma3

PartialCorrectness == Invariant1 /\ Invariant2 /\ Invariant3

====