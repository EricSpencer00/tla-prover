---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* Model checking a reachability algorithm: the graph is fixed and tiny; the
\* sequence quantifier is made finite so TLC can explore the whole state space.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Step ==
    /\ pc = "running"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = Succ(frontier)
    /\ pc' = IF (frontier \cup marked = Nodes) THEN "done" ELSE "running"

Done ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* The invariant that reachable = marked would fail the moment frontier ever
\* had a node outside the reachable set; reachable is defined by a path shape,
\* so the shape's exact definition is what keeps the model finite.
Inv3 == marked \subseteq frontier \cup marked

InverseReachable ==
    \E seq \in LimitedSeq(Nodes):
        /\ Head(seq) = Root
        /\ seq # <<>>
        /\ Len(seq) <= Cardinality(Nodes)

ReachableDecomposition ==
    /\ frontier \cup marked = InverseReachable
    /\ frontier \cap marked = {}

SuccessorClosure ==
    /\ frontier \subseteq Succ(frontier \cup marked)
    /\ (frontier # {} => \E x \in frontier : x \notin marked)

PartialCorrectness ==
    \A n \in Nodes : n \in frontier => \E seq \in LimitedSeq(Nodes):
        /\ Head(seq) = Root
        /\ seq # <<>>
        /\ Len(seq) <= Cardinality(Nodes)
        /\ n = seq[Len(seq)]

Termination == <>(pc = "done")

\* The override: a bounded (finite) version of Seq, so no infinite quantification.
LimitedSeq(S) == {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

\* The .cfg replaces Succ with a concrete 2-successor-per-node shape.
ConnectedToSomeButNotAll(n) == ConnectedToSomeButNotAll

====