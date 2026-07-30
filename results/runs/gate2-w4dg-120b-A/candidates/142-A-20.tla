---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Nodes \ {Root}
    /\ pc = "idle"

StartSearch ==
    /\ pc = "idle"
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

Expand(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

FinishSearch ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitStep == StartSearch \/ FinishSearch

Next ==
    \/ InitStep
    \/ (\E n \in Nodes: Expand(n))

Spec == Init /\ [][Next]_vars

\* Invariant 1: the marked set stays within the reachable nodes, and every
\* successor of a marked node is already marked or in the frontier.
ClosedFrontier ==
    /\ marked \subseteq Nodes
    /\ \A n \in marked: \A m \in Nodes: (n # Root /\ n \in marked) => m \in marked \/ m \in frontier

\* Lemma 1 (from the reachability proofs module) yields this as a consequence.
FrontierClosure == Nodes \ (marked \cup frontier) = {}

\* Lemma 2: reachable-from is stable under adding successors; Lemma 3: reachable
\* from the empty set is empty.
ReachableComplete == ReachableFrom(Root, Nodes) = marked \cup ReachableFrom(frontier, Nodes)

DoneMatchesReachable == pc = "done" => marked = ReachableFrom(Root, Nodes)

INVARIANTS == ClosedFrontier
PROPERTIES == ReachableComplete /\ DoneMatchesReachable
====