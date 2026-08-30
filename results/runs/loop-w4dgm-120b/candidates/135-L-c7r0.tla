---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"active", "done"}

Inv1 ==
    \A n \in frontier :
        /\ frontier \subseteq marked
        /\ frontier \subseteq Succ[n]
        /\ n \notin Succ[n]

Inv2 ==
    /\ marked = Nodes
    /\ frontier = {}

Inv3 ==
    \A n \in Nodes :
        n \in marked =>
            \E s \in [1..Cardinality(Nodes) -> Nodes] :
                /\ s[1] = Root
                /\ \A i \in 1..Cardinality(Nodes) : s[i] \in Nodes
                /\ \A i \in 1..Cardinality(Nodes) : \E e \in Succ[s[i]] : s[i + 1] = e

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "active"

MarkStep ==
    /\ pc = "active"
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE
       IN /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ frontier' = frontier' \ {n}
    /\ UNCHANGED <<pc>>

Done ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "done"
    /\ marked' = {Root}
    /\ frontier' = Succ[Root]
    /\ pc' = "active"

Next ==
    \/ MarkStep
    \/ Done
    \/ Reset

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

LimitedSeq == Sequences.Seq

ConnectedToSomeButNotAll == Succ

====