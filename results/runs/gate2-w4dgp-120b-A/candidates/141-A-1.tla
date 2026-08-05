---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

ReachableFrom(S) == { n \in Nodes : \E s \in S : n \in Succ[s] }

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
           /\ marked' = marked
    /\ pc' = "running"

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 ==
    \A S \in SUBSET Nodes :
        ReachableFrom(S) \subseteq ReachableFrom(marked \cup S)
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == (pc = "done") => (marked = ReachableFrom({Root}))

Termination == (ReachableFrom({Root}) # Nodes) ~> (pc = "done")

====