---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's variant: the frontier may overlap the marked set, so a node is
\* never removed from the frontier when it is first discovered.
Explore(n) ==
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier' \cup Succ[n]
       ELSE /\ marked' = marked
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == (\E n \in Nodes: Explore(n)) \/ Terminate

Spec == Init /\ [][Next]_vars

\* Every successor of a marked node is either already marked or still in the
\* frontier, so no reachable node is ever lost.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The nodes reachable from the marked set together with the frontier are
\* exactly the nodes reachable from their union.
Inv2 ==
    (marked \cup frontier) \cup
        {y \in Nodes : \E x \in (marked \cup frontier) : y \in Succ[x]}
        = {y \in Nodes : \E x \in (marked \cup frontier) : y \in Succ[x]}

\* The reachable set from the root is the marked set plus whatever is still
\* reachable from the frontier.
Inv3 ==
    {y \in Nodes : \E x \in {Root} : y \in Succ[x]}
        = marked \cup {y \in Nodes : \E x \in frontier : y \in Succ[x]}

PartialCorrectness ==
    (pc = "done") => (marked = {y \in Nodes : \E x \in {Root} : y \in Succ[x]})

\* If the reachable set is finite, the algorithm eventually terminates.
Termination ==
    (\A n \in Nodes : n \in {y \in Nodes : \E x \in {Root} : y \in Succ[x]})
        ~> (pc = "done")

\* The .cfg replaces Succ with a bounded version for finite checking.
ConnectedToSomeButNotAll == Succ

\* The .cfg replaces Seq with a finite version for the model checker.
LimitedSeq == Seq

====