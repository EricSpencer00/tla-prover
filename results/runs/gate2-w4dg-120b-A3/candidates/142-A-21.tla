---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachableAlg, ReachableLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"ready", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "ready"

Start ==
    /\ pc = "ready"
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

Mark(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Expand(n) ==
    /\ pc = "running"
    /\ n \in marked
    /\ frontier' = frontier \cup (SuccOf(n) \ {n})
    /\ UNCHANGED <<marked, pc>>

Finish ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitStep == Start \/ Mark(Root) \/ Expand(Root) \/ Finish

Next ==
    \/ InitStep
    \/ \E n \in Nodes : Mark(n) \/ Expand(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : SuccOf(n) \subseteq marked \cup frontier

Inv2 ==
    /\ marked \cup ReachOf(frontier) = ReachOf(marked \cup frontier)
    /\ frontier \cap marked = {}

Inv3 ==
    /\ ReachOf(Root) = marked \cup ReachOf(frontier)
    /\ frontier \cap ReachOf(Root) = {}

Theorem ==
    /\ Inv1
    /\ Inv2
    /\ Inv3
    /\ (pc = "done") => (marked = ReachOf(Root))

INVARIANTS == Inv1
PROPERTIES == Inv2 /\ Inv3 /\ Theorem
====