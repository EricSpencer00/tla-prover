---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Succ is an uninterpreted graph-successor relation; ConnectedToSomeButNotAll
\* is the bounded version the .cfg substitutes in for it.
ConnectedToSomeButNotAll == {y \in Nodes : \E x \in Nodes : y \in Succ[x]}

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"running", "done"}

Init == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = "running"

\* The overlap is intentional: the node stays in the frontier while being
\* explored (added to marked), so the two sets need not be disjoint.
Explore(n) == /\ pc = "running"
              /\ n \in frontier
              /\ n \notin marked
              /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
              /\ pc' = pc

DropStale(n) == /\ pc = "running"
                /\ n \in frontier
                /\ n \in marked
                /\ frontier' = frontier \ {n}
                /\ pc' = pc
                /\ marked' = marked

Next == \/ \E n \in Nodes : Explore(n)
        \/ \E n \in Nodes : DropStale(n)
        \/ /\ pc = "running" /\ frontier = {}
           /\ pc' = "done"
           /\ marked' = marked
           /\ frontier' = frontier

Spec == Init /\ [][Next]_vars

\* Invariant 1: edges from a marked node never point outside the explored region.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Invariant 2: the marked set plus the reachable-from-frontier region is
\* exactly the reachable-from-(marked-or-frontier) region.
Inv2 == (marked \cup {y \in Nodes : \E x \in frontier : y \in Succ[x]})
          = {y \in Nodes : \E x \in (marked \cup frontier) : y \in Succ[x]}

\* Invariant 3: the reachable set is always partitioned into the marked set
\* and the region reachable from the frontier.
Inv3 == {y \in Nodes : \E x \in Nodes : y \in Succ[x]}
          = marked \cup {y \in Nodes : \E x \in frontier : y \in Succ[x]}

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == (pc = "running" /\ frontier # {}) ~> (pc = "done")

\* The .cfg replaces Seq with this bounded version for the finite case.
LimitedSeq(S) == CHOOSE f \in Seq(S) : \A g \in Seq(S) : Len(g) <= Len(f)

====