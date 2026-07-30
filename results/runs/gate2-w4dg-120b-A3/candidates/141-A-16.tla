---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 2 }

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ frontier /= {}
    /\ pc = "running"
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) \subseteq
        (MarkedReachable \cup FrontierReachable \cup frontier)

Inv3 ==
    \A x \in ReachableFrom(Root) : x \in marked \cup FrontierReachable

PartialCorrectness ==
    (pc = "done") => (marked = ReachableFrom(Root))

Termination ==
    WF_vars(Explore)

MarkedReachable ==
    { x \in Nodes : \E m \in marked : x \in ReachableFrom(m) }

FrontierReachable ==
    { x \in Nodes : \E f \in frontier : x \in ReachableFrom(f) }

ReachableFrom(n) ==
    { x \in Nodes :
        \E s \in LimitedSeq(Nodes) :
            /\ Len(s) >= 1
            /\ s[1] = n
            /\ x \in { s[Len(s)] } \cup { s[i+1] : i \in 1..(Len(s) - 1) }
            /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]] }

====