---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's variant of BFS lets the marked set and the frontier overlap, which
\* matters for the parallel implementation; the invariant ties them together.
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "halted"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Exploit(n) == n \notin marked
Explore(n) == n \in frontier

AddFrontier(S) == S \cup {n \in Nodes : \E m \in S : n \in Succ[m]}

Next ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ IF Exploit(n)
           THEN /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
           ELSE /\ marked' = marked
                /\ frontier' = frontier \ {n}
        /\ pc' = IF frontier' = {} THEN "halted" ELSE pc

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* closure of a set under the Succ relation; used in the invariants.
ReachableSet(S) ==
    LET g[T \in SUBSET Nodes] ==
        IF T = {}
        THEN S
        ELSE LET x == CHOOSE y \in T : TRUE
             IN g[T \ {x}] \cup Succ[x]
    IN g[Nodes]

Inv1 == \A m \in marked : Succ[m] \subseteq (marked \cup frontier)

Inv2 == (marked \cup frontier) = ReachableSet(marked \cup frontier)

Inv3 == ReachableSet({Root}) = (marked \cup ReachableSet(frontier))

PartialCorrectness == marked = ReachableSet({Root})

Termination == (pc = "running") ~> (pc = "halted")

\* Operator substitution: the .cfg replaces Succ with a bounded version.
Succ == ConnectedToSomeButNotAll

\* The .cfg replaces Seq with a bounded version of the sequence constructor.
LimitedSeq(n) == CHOOSE s \in Seq(1..n) : TRUE

====