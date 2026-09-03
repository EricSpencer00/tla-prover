---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

Init == /\ marked = {Root}
        /\ frontier = Succ(Root)
        /\ pc = "running"

Expand == /\ pc = "running"
          /\ frontier # {}
          /\ LET n == CHOOSE x \in frontier : TRUE
                 frontier' == (frontier \cup Succ(n)) \ marked
                 marked'   == marked \cup {n}
             IN <<marked, frontier' >>
          /\ pc' = IF frontier' = {} /\ (Nodes \ marked) = {} THEN "done" ELSE "running"

Next == Expand

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq Nodes \ marked

Reaches(n) == \E s \in LimitedSeq(Nodes) : s # <<>> /\ s[1] = Root /\ s[Len(s)] = n

Inv2 == \A n \in marked : Reaches(n)

Decomposition == marked \cup frontier \cup (Nodes \ marked \ frontier) = Nodes

Inv3 == Decomposition

Reachable == {n \in Nodes : Reaches(n)}

Inv4 == reachable = marked \cup frontier

PartialCorrectness == reachable = marked \cup frontier

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

\* Seq from Sequences is infinite; this bounded version makes the model finite.
LimitedSeq == [S \in SUBSET Nodes |-> UNION {Seq(S, k) : k \in 0..Cardinality(S)}]

====