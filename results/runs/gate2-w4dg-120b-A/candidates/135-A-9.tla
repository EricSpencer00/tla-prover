---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"ready", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "ready"

ExpandStep(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ frontier' = frontier \cup Succ[n]
    /\ marked' = marked \cup Succ[n]
    /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier \ {n} = {} THEN "done" ELSE "running"

Start ==
    /\ pc = "ready"
    /\ pc' = "running"
    /\ UNCHANGED <<marked, frontier>>

Idle ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ Idle
    \/ \E n \in Nodes : ExpandStep(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
    \A n \in Nodes : n \in marked => Succ[n] \subseteq marked

Inv2 ==
    \A n \in Nodes : n \in frontier => n \in marked

Inv3 ==
    marked = {x \in Nodes : \E s \in Seq : s # << >> /\ Head(s) = Root /\ x \in Set(seqSeq(s))}

PartialCorrectness ==
    \A n \in Nodes :
        \/ (n \in marked => \E s \in Seq : s # << >> /\ Head(s) = Root /\ n \in Set(seqSeq(s)))
        \/ (n \notin marked => \A s \in Seq : Head(s) = Root => n \notin Set(seqSeq(s)))

Termination ==
    <>(pc = "done")

====