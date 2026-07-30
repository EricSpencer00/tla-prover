---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* Model-checking configuration: concrete nodes, a bounded sequence override, and
\* the exact set of operators the reference .cfg will substitute for.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in 0..2

\* The algorithm starts with only the root node marked and in the frontier; the
\* program counter is at the start of the worklist loop.
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = 0

\* Take one node from the frontier and mark its successors, or finish when the
\* frontier is empty.
StepOnce ==
    /\ pc = 0
    /\ frontier # {}
    /\ frontier' = frontier \ {Root}
    /\ marked' = marked \cup Succ(Root)
    /\ pc' = 1
    /\ UNCHANGED << pc >>

Step ==
    /\ StepOnce \/ (pc = 1 /\ UNCHANGED vars /\ frontier' = {} /\ pc' = 2)
    /\ UNCHANGED << marked, frontier, pc >>

Next == Step

Spec == Init /\ [][Next]_vars

\* The graph is 4 nodes arranged so that each node has exactly 2 successors,
\* which keeps reachability interesting while limiting the state space.
ConnectedToSomeButNotAll ==
    [x \in Nodes |-> IF x = Root THEN Nodes \ {Root} ELSE {Root, x}]

Inv1 == \A x \in frontier : \E y \in marked : y \in Succ(x)
Inv2 == \A x \in marked : \E y \inmarked : x \in Succ(y) \/ x = Root
Inv3 == \A x \in Nodes : x \in marked \/ x \in frontier

PartialCorrectness == frontier = {} => marked = Nodes

Termination == <>(frontier = {})

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ and LimitedSeq for Seq,
\* so Succ and Seq are never declared here and the overrides stay in force.
====