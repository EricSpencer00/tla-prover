---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

NodesList == {"n1", "n2", "n3", "n4"}

\* The finite override for reachability: LimitedSeq is a bounded version of Seq
\* inserted by the .cfg, so this override is the only Seq in the model.
LimitedSeq == Sequences.Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq NodesList
    /\ frontier \subseteq NodesList
    /\ pc \in {"ready", "working", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = Succ[Root]
    /\ pc = "ready"

Explore(n) ==
    /\ pc = "ready"
    /\ n \in frontier
    /\ frontier' = frontier \cup Succ[n]
    /\ marked' = marked \cup {n}
    /\ pc' = "working"

Finish ==
    /\ pc = "working"
    /\ frontier \subseteq marked
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in NodesList : Explore(n)
    \/ Finish

Spec == Init /\ [][Next]_vars

\* Successor closure: every marked node's successors are already marked.
Inv1 == \A n \in marked : Succ[n] \subseteq marked

\* Reachability decomposition: every unmarked node lies on a frontier edge.
Inv2 == \A n \in NodesList \ marked : \E m \in marked : n \in Succ[m]

\* Reachable set equals marked set: every node reachable from the root is
\* already marked, so the search is never still possible once it is done.
Inv3 == {n \in NodesList : \E p \in LimitedSeq : p[1] = Root /\ p[Len(p)] = n /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]} = marked

PartialCorrectness == \A n \in NodesList : (\E p \in LimitedSeq : p[1] = Root /\ p[Len(p)] = n /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]] => n \in marked

Termination == (pc = "working") ~> (pc = "done")

====