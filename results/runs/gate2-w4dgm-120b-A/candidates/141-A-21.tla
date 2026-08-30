---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* LimitedSeq is the bounded version of Seq that the .cfg substitutes.
LimitedSeq(S) == CHOOSE s \in Seq(S) : \A k \in 1..Len(s) : s[k] \in S

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
    IF S = {} THEN {}
    ELSE LET n == CHOOSE x \in S : TRUE IN
         {n} \cup ReachableFrom(S \cup Succ[n]) \ {n}

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The choice below is nondeterministic: either case may fire on the chosen
\* frontier node, which is what lets the two cases interleave freely.
Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
         IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = IF (frontier \cup Succ[n]) = {} /\ n \in marked
              THEN "done" ELSE "running"

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ Terminate

Spec == Init /\ [][Next]_vars

\* Safety: marked nodes always dominate the graph, so any frontier node is
\* backed by a marked node and cannot wander off into an unreachable sink.
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* No marked node is left behind: the nodes reachable from marked plus the
\* nodes reachable from the frontier already cover the reachable-from-marked
\* region, so the frontier only holds frontier nodes of the reachable region.
Inv2 == ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == \A n \in Nodes : (n \in marked) <=> (n \in ReachableFrom({Root}))

\* Fairness: every non-empty frontier must eventually shrink or empty.
Termination == (frontier # {}) ~> (frontier = {})
====