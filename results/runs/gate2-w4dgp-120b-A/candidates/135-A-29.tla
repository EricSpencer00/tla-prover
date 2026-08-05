---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES markedSet, frontier, pc

vars == << markedSet, frontier, pc >>

TypeOK ==
    /\ markedSet \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"init", "exploring", "done"}

Init ==
    /\ markedSet = {Root}
    /\ frontier = {Root}
    /\ pc = "init"

Successors(n) == { m \in Nodes : Succ(n, m) }

NextStep ==
    \/ \E m \in Nodes :
        /\ pc = "exploring"
        /\ \E n \in frontier :
            /\ m \in Successors(n)
            /\ m \notin markedSet
            /\ markedSet' = markedSet \cup {m}
            /\ frontier' = (frontier \cup {m}) \ {n}
        /\ pc' = "exploring"
    \/ \E n \in frontier :
        /\ \A m \in (Successors(n) \ markedSet) : FALSE
        /\ frontier' = frontier \ {n}
        /\ pc' = "exploring"
    \/ pc = "exploring" /\ frontier = {} /\ pc' = "done" /\ UNCHANGED << markedSet, frontier >>
    \/ pc = "init" /\ pc' = "exploring" /\ UNCHANGED << markedSet, frontier >>
    \/ pc = "done" /\ UNCHANGED vars

Next == NextStep

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A m \in markedSet : \A n \in frontier : m \notin Successors(n)

Inv2 ==
    markedSet = { n \in Nodes : \E seq \in (Nodes -> Nat) : seq[Root] = n /\ Len(seq) <= Cardinality(Nodes) /\ (\A i \in 1..(Len(seq) - 1) : Succ(seq[i], seq[i+1])) }

Inv3 ==
    markedSet = { n \in Nodes : \E seq \in (Nodes -> Nat) : seq[Root] = n /\ Len(seq) <= Cardinality(Nodes) /\ (\A i \in 1..(Len(seq) - 1) : Succ(seq[i], seq[i+1])) }

PartialCorrectness ==
    \A n \in Nodes : (n \in markedSet) => \E seq \in (Nodes -> Nat) : seq[Root] = n /\ Len(seq) <= Cardinality(Nodes) /\ (\A i \in 1..(Len(seq) - 1) : Succ(seq[i], seq[i+1]))

Termination == <>(pc = "done")

====