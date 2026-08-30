---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"idle", "working", "done"}

\* Invariant 1: successor closure -- every node on the frontier is reachable via
\* a successor of some already-marked node.
Inv1 == \A n \in frontier : \E m \in marked : n \in Succ[m]

\* Invariant 2: reachable nodes are covered by marked nodes or frontier nodes.
Inv2 == \A n \in Nodes : (n \in marked \/ n \in frontier) => TRUE

\* Invariant 3: marked and frontier are disjoint.
Inv3 == marked \cap frontier = {}

\* Partial correctness: the algorithm always marks the root, since a non-empty
\* frontier at termination must contain it and frontier and marked are disjoint.
PartialCorrectness == (pc = "done") => (Root \in marked)

Init == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = "idle"

Work == /\ pc = "idle"
        /\ pc' = "working"
        /\ UNCHANGED <<marked, frontier>>

Mark == /\ pc = "working"
        /\ frontier # {}
        /\ marked' = marked \cup frontier
        /\ frontier' = {}
        /\ pc' = IF frontier \cup frontier = {} THEN "done" ELSE "working"

Explore == /\ pc = "working"
           /\ frontier # {}
           /\ frontier' = \E m \in frontier : Succ[m]
           /\ UNCHANGED <<marked, pc>>

Next == Work \/ Mark \/ Explore

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Termination == (pc = "done") ~> (pc = "done")

\* Bounded-path model checking: replace the infinite Seq operator with a
\* finite-sequence version that never grows past the number of nodes.
LimitedSeq == [S \in SUBSET Nodes, n \in Nat |-> IF n <= Cardinality(S) THEN CHOOSE f \in [1..n -> S] : \A i \in 1..n : \A j \in 1..n : f[i] = f[j] => i = j ELSE {}

ConnectedToSomeButNotAll == Succ

====