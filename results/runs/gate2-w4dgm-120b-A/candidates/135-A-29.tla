---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

\* Overridden by a bounded quantifier: the number of nodes is finite, so the
\* number of steps to get from any source to any destination is bounded.
Bound   == Cardinality(Nodes)
MaxLen  == Bound

RECURSIVE ExistsPath(_: Nodes, _: Nodes)
ExistsPath(s, d) ==
    IF s = d THEN TRUE
    ELSE \E n \in Nodes : (n \in Succ[s]) /\ ExistsPath(n, d)

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

StartStep ==
    /\ pc = "idle"
    /\ frontier # {}
    /\ pc' = "working"
    /\ UNCHANGED <<marked, frontier>>

MarkStep ==
    /\ pc = "working"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup Succ[n]
    /\ UNCHANGED pc

CompleteStep ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ marked' = {}
    /\ frontier' = {Root}
    /\ pc' = "idle"

Next == StartStep \/ MarkStep \/ CompleteStep \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(StartStep) /\ SF_vars(MarkStep) /\ WF_vars(CompleteStep)

\* The renaming in the .cfg turns Succ into ConnectedToSomeButNotAll, which is
\* exactly the property being checked here.
Inv1 == \A n \in marked : ExistsPath(Root, n)

Inv2 == marked \cap frontier = {}
Inv3 == marked \cup frontier = Nodes
PartialCorrectness == frontier \subseteq (Nodes \ marked)

Termination == pc = "done"

\* The .cfg replaces Seq with this finite version, so the model stays finite.
LimitedSeq(S, k) == {s \in Seq(S) : Len(s) <= k}

====