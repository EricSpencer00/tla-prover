---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* A deterministic out-degree-2 graph: each node's successors are its two successors
\* in cyclic order, wrapping around the 4-node ring.
Neighbour == (Root + 1) % 4
Neighbour2 == (Root + 2) % 4
SmallestSuccessor(n) == CHOOSE x \in Succ[n] : \A y \in Succ[n] : x <= y

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "running"

Mark(n) ==
    /\ n \in frontier
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \cup Succ[n]) \ {n}
    /\ pc' = pc

Done ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Halt ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Neighbour \cup {Neighbour2} : Mark(n)
    \/ Done
    \/ Halt

Spec == Init /\ [][Next]_vars

\* The reachable set is exactly the marked set; no node is reachable but unmarked.
Reachable == { n \in Nodes : \E seq \in NatSeq(Nodes) : Reaches(seq, Root, n) }

Reaches(seq, x, y) ==
    \/ (seq = << >> /\ x = y)
    \/ (\E z \in Nodes : seq = << z >> /\ z \in Succ[x] /\ z = y)
    \/ (\E t \in Nodes, rest \in NatSeq(Nodes) :
           seq = << t >> \o rest /\ t \in Succ[x] /\ Reaches(rest, t, y))

\* Bounded version of the usual Seq operator from Sequences, making the model finite.
LimitedSeq(of, ran) == { s \in Seq(of) : Len(s) <= Cardinality(ran) }

Inv1 == \A n \in frontier : n \notin marked
Inv2 == \A n \in marked : \E seq \in NatSeq(Nodes) : Reaches(seq, Root, n)
Inv3 == \A n \in Nodes : (n \in Reachable) => (n \in marked)
PartialCorrectness == marked \subseteq Reachable

Termination == <>(pc = "done")

====