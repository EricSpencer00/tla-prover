---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Seqs == UNION {[1 .. n -> Nodes] : n \in 0 .. Cardinality(Nodes)}
LimitedSeq == Seqs
ConnectedToSomeButNotAll == Succ

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "searching"

Step ==
    /\ pc = "searching"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ frontier' = frontier \ {n}
        /\ marked' = marked \cup ConnectedToSomeButNotAll[n]
    /\ UNCHANGED pc

Complete ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "completed"
    /\ UNCHANGED <<marked, frontier>>

Reset ==
    /\ pc = "completed"
    /\ marked' = {Root}
    /\ frontier' = {Root}
    /\ pc' = "searching"

Next == Step \/ Complete \/ Reset

Spec == Init /\ [][Next]_vars /\ SF_vars(Complete)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"searching", "completed"}

Inv1 ==
    \A n \in Nodes : n \in frontier => \A m \in frontier : m \notin ConnectedToSomeButNotAll[n]

Inv2 ==
    \A n \in marked : n \in ConnectedToSomeButNotAll[Root]

Inv3 ==
    \A n \in Nodes : n \in marked <=> \E s \in LimitedSeq : s[1] = Root /\ s[Len(s)] = n

PartialCorrectness ==
    (\A m \in Nodes : \A n \in Nodes : n \in ConnectedToSomeButNotAll[m] => \A f \in LimitedSeq : (f[1] = m /\ f[Len(f)] = n => n \in marked)) /\ frontier = {}

Termination ==
    (\A m \in Nodes : \A n \in Nodes : n \in ConnectedToSomeButNotAll[m] => \A f \in LimitedSeq : (f[1] = m /\ f[Len(f)] = n => n \in marked))
        ~> (\A n \in Nodes : n \in marked)
====