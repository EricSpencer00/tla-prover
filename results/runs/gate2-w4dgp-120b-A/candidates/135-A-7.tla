---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in 0..3

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

Next ==
    /\ frontier # {}
    /\ frontier' = {}
    /\ marked' = marked \cup frontier
    /\ pc' = (pc + 1) % 4

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 ==
    \A b \in Nodes : b \in frontier => b \in marked
Inv2 ==
    \A b \in Nodes :
        (b \in marked => \/ \E c \in frontier : b \in Succ[c])
        /\ (b \in frontier => \/ \E c \in marked : b \in Succ[c])
Inv3 ==
    \A b \in Nodes :
        b \in marked <=> \E s \in LimitedSeq(Nodes) :
            /\ Len(s) <= Cardinality(Nodes)
            /\ s[1] = Root
            /\ b \in set(s)
            /\ \A j \in 1..(Len(s) - 1) : s[j+1] \in Succ[s[j]]
PartialCorrectness ==
    \A b \in Nodes : (b \in marked => b \in ConnectedToSomeButNotAll)

Termination == <>(pc = 3)

====