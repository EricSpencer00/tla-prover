---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
         \/ /\ n \notin marked
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
         \/ /\ n \in marked
            /\ frontier' = frontier \ {n}
            /\ UNCHANGED marked
    /\ pc' = "idle"

Terminate ==
    /\ frontier = {}
    /\ pc = "idle"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* A reachable node whose successor is missing would stall the frontier
\* forever, so every successor of a marked node must already be marked
\* or waiting in the frontier.
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Reachable-from-the-frontier nodes are the remainder after peeling off
\* the marked set; the frontier may still contain marked nodes.
Inv2 == (marked \cup frontier) \cup (ReachSet(Seq, frontier) \cup ReachSet(Seq, marked))
            = ReachSet(Seq, marked \cup frontier)

\* Marked nodes plus the frontier's reachable nodes are exactly the nodes
\* reachable from the root (closure property of the graph).
Inv3 == ReachSet(Seq, {Root}) = marked \cup ReachSet(Seq, frontier)

PartialCorrectness == pc = "done" => marked = ReachSet(Seq, {Root})

Termination == (ReachSet(Seq, {Root}) \subseteq Nodes) ~> (pc = "done")
====