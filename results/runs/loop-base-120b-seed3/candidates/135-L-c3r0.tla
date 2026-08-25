---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Finite sequence operator used in place of the unbounded Seq
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Concrete successor relation: each node has exactly two distinct successors
\* ----------------------------------------------------------------------
Succ1(n) == CHOOSE m \in Nodes \ {n} : TRUE
Succ2(n) == CHOOSE m \in Nodes \ {n, Succ1(n)} : TRUE
ConnectedToSomeButNotAll(n) ==
    IF n \in Nodes THEN {Succ1(n), Succ2(n)} ELSE {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "start"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Expand ==
    /\ pc = "start"
    /\ \E n \in Frontier :
        /\ UNCHANGED Marked
        /\ Frontier' = Frontier \cup (ConnectedToSomeButNotAll(n) \ (Marked \cup Frontier))
        /\ pc' = "mark"

MarkStep ==
    /\ pc = "mark"
    /\ \E n \in Frontier :
        /\ Marked' = Marked \cup {n}
        /\ Frontier' = Frontier \ {n}
        /\ pc' = IF Frontier' = {} THEN "done" ELSE "start"

Next ==
    \/ Expand
    \/ MarkStep

vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"start", "mark", "done"}

Inv1 == \A n \in Marked : \A s \in ConnectedToSomeButNotAll(n) : s \in Marked

Inv2 == Frontier \cap Marked = {}

\* ----------------------------------------------------------------------
\* Reachability helper definitions using the bounded sequence operator
\* ----------------------------------------------------------------------
Paths ==
    { p \in LimitedSeq(Nodes) :
        /\ Len(p) > 0
        /\ Head(p) = Root
        /\ \A i \in 1..(Len(p)-1) : p[i+1] \in ConnectedToSomeButNotAll(p[i]) }

Reachable ==
    { n \in Nodes : \E p \in Paths : p[Len(p)] = n }

Inv3 == Marked \cup Frontier = Reachable

PartialCorrectness == (pc = "done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")
====