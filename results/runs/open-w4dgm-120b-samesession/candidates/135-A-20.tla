---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* Model checking the Misra reachability algorithm: a finite 4-node graph
\* where every node has exactly two successors, and sequences are bounded
\* to the number of nodes so the exhaustive check always terminates.
CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"running", "done"}

\* A sequence of nodes, reused from Sequences, which the .cfg overrides to
\* a finite version so the model stays checkable.
Seq == Sequences.Seq

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "running"

Step(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ marked' = marked \cup Succ[n]
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in Nodes : Step(n)
    \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* The three core reachability invariants plus partial correctness.
Inv1 == frontier \subseteq marked
Inv2 == marked \cap Frontier = {}
Inv3 == marked \cup Frontier = Nodes
PartialCorrectness == marked = Nodes
Termination == <>(pc = "done")

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ directly.
ConnectedToSomeButNotAll == Succ
====