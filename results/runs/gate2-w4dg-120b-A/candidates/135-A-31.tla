---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc, seq

vars == <<marked, frontier, pc, seq>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "running", "done"}
    /\ seq \in Seq

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "running"
    /\ seq = <<Root>>

Expand(n) ==
    /\ frontier = {}
    /\ marked' = marked \cup {n}
    /\ frontier' = Succ[n]
    /\ seq' = IF Len(seq) < 4 THEN Append(seq, n) ELSE seq
    /\ UNCHANGED pc

Done ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier, seq>>

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ Done
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Inv2 ==
    \A u \in marked : \A v \in Succ[u] : v \in marked

Inv3 ==
    marked = {n \in Nodes : \E p \in Seq : Head(p) = n}

PartialCorrectness ==
    \A n \in marked : (\E m \in Nat : n \in Succ[m])

Termination ==
    \A m \in Nat : pc = "done"
====