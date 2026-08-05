---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"ready", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "ready"

ExpandStep(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ frontier' = frontier \cup Succ[n]
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = frontier' \ {n}
    /\ UNCHANGED pc

Step1 == \E n \in Nodes : ExpandStep(n)

Start ==
    /\ pc = "ready"
    /\ pc' = "running"
    /\ frontier' = frontier \cup Succ[Root]
    /\ marked' = marked \cup Succ[Root]
    /\ UNCHANGED <<marked, frontier, pc>>

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Step1 \/ Start \/ Terminate]_vars

Inv1 ==
    \A n \in Nodes : n \in marked => \E m \in frontier : m \in Succ[n]

Inv2 ==
    \A n \in Nodes : (n \in frontier) => (n \in marked)

Inv3 ==
    marked = {n \in Nodes : (\E s \in {1, 2} : \E seq \in LimitedSeq(Succ) : Len(seq) = s /\ Head(seq) = n)}

PartialCorrectness ==
    frontier = {} => \A n \in Nodes : (\E seq \in LimitedSeq(Succ) : Head(seq) = n) => n \in marked

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ
LimitedSeq(T) == {s \in Seq(T) : Len(s) <= Cardinality(Nodes)}
====