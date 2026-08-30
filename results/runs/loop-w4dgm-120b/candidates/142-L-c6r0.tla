---- MODULE ReachableProofs ----
EXTENDS Integers, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = 0

Expand(n) ==
    /\ pc = 0
    /\ n \in frontier
    /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ marked' = marked \cup {n}
    /\ pc' = 1

Done ==
    /\ pc = 0
    /\ frontier = {}
    /\ pc' = 2
    /\ UNCHANGED <<marked, frontier>>

Backtrack ==
    /\ pc = 1
    /\ pc' = 0
    /\ UNCHANGED <<marked, frontier>>

Finish ==
    /\ pc = 2
    /\ UNCHANGED vars
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ Done
    \/ Backtrack
    \/ Finish

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in 0..2
    /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Lemma2 ==
    \A A, n \in Nodes : ReachableFrom(A \cup {n}) = ReachableFrom(A) \cup ReachableFrom({n})
====