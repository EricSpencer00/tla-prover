---- MODULE Reachable ----
EXTENDS Naturals, Sequences

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

Explore(n) ==
    /\ n \in frontier
    /\ pc = "running"
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Spec == Init /\ [Explore]_vars

Inv1 ==
    \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
    (marked \cup frontier) = Nodes

Inv3 ==
    Nodes = marked \cup (Nodes \cap frontier)

PartialCorrectness ==
    marked = Nodes

Termination ==
    (Nodes # {}) ~> (Nodes = {})

\* The .cfg substitutes ConnectedToSomeButNotAll for Succ, and replaces Seq with
\* LimitedSeq, so we define the latter as a FINITE version of Seq here.
LimitedSeq(S) == CHOOSE s \in Seq(S) : \A x \in S : \E i \in 1..Len(s) : s[i] = x

====