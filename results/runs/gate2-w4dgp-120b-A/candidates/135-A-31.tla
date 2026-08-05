---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Seq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in 0..2

Init == /\ marked = {Root}
        /\ frontier = Succ[Root]
        /\ pc = 0

Step == /\ frontier # {}
        /\ marked' = marked \cup frontier
        /\ frontier' = UNION { Succ[n] : n \in frontier }
        /\ pc' = (pc + 1) % 3

AllMarked == \A n \in Nodes : n \in marked

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Inv1 == marked \subseteq Nodes
Inv2 == frontier \subseteq Nodes
Inv3 == frontier \cap marked = {}
PartialCorrectness == AllMarked => frontier = {}

Termination == <>(pc = 0 /\ frontier = {})

====