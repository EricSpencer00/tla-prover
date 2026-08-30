---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

NONE == "none"

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "marking", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "marking"

Mark(n) ==
    /\ pc = "marking"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ pc' = IF frontier \cup Succ[n] = {} THEN "done" ELSE pc

AllDone ==
    /\ pc = "marking"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes: Mark(n)
    \/ AllDone

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq Nodes \ marked

Inv2 == marked = {n \in Nodes : \E m \in Nodes, k \in Nat : m \in marked /\ k <= 3 /\ n = Succ[m][k]}

Inv3 == (Root \in marked) \/ (Frontier \subseteq Nodes)

PartialCorrectness == (pc = "done") => (frontier = {})

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq(e) == [n \in 1..Cardinality(e) |-> CHOOSE x \in e : TRUE]

====