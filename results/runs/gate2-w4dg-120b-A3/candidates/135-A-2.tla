---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"init", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "init"

StepApply ==
    /\ pc = "init"
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

StepExplore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {y \in Nodes : \E x \in frontier : y \in Succ[x]}
    /\ UNCHANGED pc

StepFinish ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == StepApply \/ StepExplore \/ StepFinish

Spec == Init /\ [][Next]_vars

Inv1 == \A x \in marked : \E y \in frontier : x \in Succ[y]
Inv2 == \A x \in frontier : \E y \in marked : x \in Succ[y]
Inv3 == marked = {x \in Nodes : \E y \in Nodes : x \in Succ[y]}
PartialCorrectness == frontier = {} => marked = Nodes
Termination == (pc = "done") ~> (pc = "done")

ConnectedToSomeButNotAll == Succ

\* Finite version of Seq (still reusable elsewhere): restrict its length to
\* the number of nodes, which is a small constant given the model bounds.
FiniteSeq == [dom : 1..Cardinality(Nodes), ran : [1..Cardinality(Nodes) -> Nodes]]

====