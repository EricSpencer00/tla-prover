---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

NONE == "none"

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"find", "final"}

Transitive ==
    \E seq \in Seq(Nodes) :
        /\ \A i \in DOMAIN seq : seq[i] \in Nodes
        /\ seq \in ExtendedSeq(Nodes)
        /\ seq[1] = Root
        /\ seq[Len(seq)] \in frontier
        /\ \A i \in 1..(Len(seq)-1) : seq[i+1] \in Succ[seq[i]]

Inv1 == \A a \in marked : \A b \in Succ[a] : b \in marked

Inv2 == \A c \in Nodes :
    (c \in frontier) =>
        (let P == {p \in Nodes : p \in marked /\ c \in Succ[p]}
         in \/ \E a \in P : TRUE
            \/ \E seq \in Seq(Nodes) :
                /\ \A i \in DOMAIN seq : seq[i] \in Nodes
                /\ seq \in ExtendedSeq(Nodes)
                /\ seq[1] \in P
                /\ seq[Len(seq)] = c
                /\ \A i \in 1..(Len(seq)-1) : seq[i+1] \in Succ[seq[i]]
            \/ \E seq \in Seq(Nodes) :
                /\ \A i \in DOMAIN seq : seq[i] \in Nodes
                /\ seq \in ExtendedSeq(Nodes)
                /\ seq[1] \in frontier
                /\ seq[Len(seq)] = c
                /\ \A i \in 1..(Len(seq)-1) : seq[i+1] \in Succ[seq[i]]))

Inv3 == \A c \in Nodes :
    (c \in frontier) => (c \in marked \/ Transitive)

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "find"

FindStep ==
    /\ pc = "find"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {c \in Nodes :
            \/ c \in frontier
            \/ \E a \in marked : c \in Succ[a]}
    /\ pc' = "find"

Done ==
    /\ pc = "find"
    /\ frontier = {}
    /\ pc' = "final"
    /\ UNCHANGED <<marked, frontier>>

Next == FindStep \/ Done

Spec == Init /\ [][Next]_vars

PartialCorrectness == marked = Nodes

Termination == <>(pc = "final")
====