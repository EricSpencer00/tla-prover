---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

SuccNonEmpty(n) == Succ[n] # {}

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

MarkOrAdvance(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup (IF SuccNonEmpty(n) THEN Succ[n] ELSE {})
    /\ UNCHANGED pc

RemoveFromFrontier(n) ==
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

LoopStep ==
    \/ \E n \in Nodes: MarkOrAdvance(n)
    \/ \E n \in Nodes: RemoveFromFrontier(n)

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == LoopStep \/ Terminate

Spec == Init /\ [][Next]_vars
    /\ WF_vars(LoopStep)

Inv1 == \A n \in marked: SuccNonEmpty(n) => (Succ[n] \subseteq (marked \cup frontier))
Inv2 == (marked \cup frontier) \subseteq (Reachable(Root, Succ) \cup frontier)
Inv3 == Reachable(Root, Succ) \subseteq (marked \cup Reachable(frontier, Succ))

PartialCorrectness == Reachable(Root, Succ) = marked

Termination == (Reachable(Root, Succ) = Nodes) ~> (pc = "done")

ConnectedToSomeButNotAll == Cardinality({n \in Nodes : (n \in marked \/ n \in frontier)}) >= 2

LimitedSeq(S) == CHOOSE s \in Seq(S) : Cardinality(S) > 0

====