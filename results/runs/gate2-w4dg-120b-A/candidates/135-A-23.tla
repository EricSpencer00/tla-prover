---- MODULE MCReachable ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Succ, Seq

ASSUME Cardinality(Nodes) = 4 /\ Root \in Nodes /\ Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "working"

Step ==
    /\ pc = "working"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \cup (Succ[n])) \ marked
    /\ pc' = IF frontier' = {} THEN "done" ELSE "working"

Loop ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "working"
    /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Step \/ Loop]_<<marked, frontier, pc>>

Inv1 ==
    /\ \A n \in frontier : \E s \in Seq : s # <<>> /\ Head(s) = n /\ \A i \in 1..Len(s) : s[i] \in marked

Inv2 ==
    /\ marked \subseteq \{n \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = Root /\ Last(s) = n /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]\}

Inv3 ==
    /\ \A n \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = Root /\ Last(s) = n /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]
       => n \in marked

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = {n \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = Root /\ Last(s) = n /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]}

Termination ==
    (pc = "working") ~> (pc = "done")

====