---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

\* A configuration module for the sequential Misra reachability algorithm.
\* It inherits the algorithm's state and actions, adding only the concrete
\* graph and the sequence bound needed to make the model finite.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* The graph is deterministic: each node has exactly two successors.
SuccOf(n) == Succ[n]

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in 0..3

Init ==
    /\ marked = {Root}
    /\ frontier = SuccOf(Root)
    /\ pc = 0

Step1 ==
    /\ pc = 0
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {n \in Nodes : \E m \in frontier : n \in SuccOf(m)}
    /\ pc' = 1
    /\ UNCHANGED <<>>

Step2 ==
    /\ pc = 1
    /\ frontier' = SuccOf(Root)
    /\ pc' = 2
    /\ UNCHANGED <<marked>>

Done ==
    /\ pc = 2
    /\ pc' = 3
    /\ UNCHANGED <<marked, frontier>>

Next == Step1 \/ Step2 \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq (Nodes \ marked)
Inv2 == marked = {n \in Nodes : \E s \in Seq : Head(s) = Root /\ \A i \in 1..(Len(s) - 1) : Head(Tail(s)) \in SuccOf(Head(s)) /\ n = Head(Tail(s))}
Inv3 == marked = {n \in Nodes : \E p \in 1..Cardinality(Nodes) : [p \in 1..p |-> n] \in Seq}
PartialCorrectness == Root \in marked

Termination == <>(pc = 3)

====