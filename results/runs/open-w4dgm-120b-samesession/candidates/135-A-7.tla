---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"working", "done"}

\* Marked set is closed under successor steps (invariant of the reachability algorithm).
Inv1 ==
    /\ marked \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq marked

\* Every node in the frontier is reachable from the root via a path of marked nodes.
Inv2 ==
    \A n \in frontier :
        \E seq \in LimitedSeq([1..Cardinality(Nodes) -> Nodes]) :
            /\ seq[1] = Root
            /\ seq[Cardinality(seq)] = n
            /\ \A i \in 1..(Cardinality(seq) - 1) :
                    seq[i + 1] \in ConnectedToSomeButNotAll[seq[i]]

\* Reachable set is contained in the marked set.
Inv3 ==
    \A n \in Nodes :
        (\E seq \in LimitedSeq([1..Cardinality(Nodes) -> Nodes]) :
            /\ seq[1] = Root
            /\ seq[Cardinality(seq)] = n
            /\ \A i \in 1..(Cardinality(seq) - 1) :
                    seq[i + 1] \in ConnectedToSomeButNotAll[seq[i]])
            => n \in marked

PartialCorrectness == Inv2 /\ Inv3

\* Bounded path quantification: always a path of bounded length exists for a frontier node.
BoundedPathExists ==
    \A n \in frontier :
        \E seq \in LimitedSeq([1..Cardinality(Nodes) -> Nodes]) :
            /\ seq[1] = Root
            /\ seq[Cardinality(seq)] = n
            /\ \A i \in 1..(Cardinality(seq) - 1) :
                    seq[i + 1] \in ConnectedToSomeButNotAll[seq[i]]

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "working"

MarkNode(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup Succ[n]
    /\ UNCHANGED pc

\* The frontier shrinks as nodes leave it (become marked), which is where progress comes from.
RemoveFromFrontier(n) ==
    /\ pc = "working"
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Complete ==
    /\ pc = "working"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Halt ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : MarkNode(n)
    \/ \E n \in Nodes : RemoveFromFrontier(n)
    \/ Complete
    \/ Halt

Spec == Init /\ [][Next]_vars

Termination ==
    \A n \in Nodes : (n \in frontier) ~> (n \notin frontier)

====