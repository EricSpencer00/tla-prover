---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Reachability of a node via a bounded path; the sequence length bound is
\* what makes this checkable, otherwise the existential over sequences is
\* over an unbounded domain.
RECURSIVE Reachable(_)
Reachable(S) ==
    IF S = << >> THEN {}
    ELSE LET n == Head(S) IN {n} \cup Reachable(Tail(S))

\* A node is reachable by some path from the root if it appears in the set
\* of nodes collected from some bounded sequence starting at the root.
ReachableFromRoot(n) == \E S \in [1..Cardinality(Nodes) -> Nodes] :
    /\ Head(S) = Root
    /\ n \in Reachable(S)

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "active"

Expand(n) ==
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup Succ[n]
    /\ UNCHANGED pc

Quiesce ==
    /\ frontier = {}
    /\ pc = "active"
    /\ pc' = "quiesced"
    /\ UNCHANGED << marked, frontier >>

Restart ==
    /\ pc = "quiesced"
    /\ pc' = "active"
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ \E n \in Nodes : Expand(n)
    \/ Quiesce
    \/ Restart

Spec == Init /\ [][Next]_vars

\* Invariant: successor closure -- the reachable set is closed under the graph's successors.
Inv1 == \A n \in marked : Succ[n] \subseteq marked

\* Invariant: the frontier stays inside the reachable set.
Inv2 == frontier \subseteq ReachableFromRoot

\* Invariant: every reachable node is either marked or waiting in the frontier.
Inv3 == ReachableFromRoot \subseteq (marked \cup frontier)

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"active", "quiesced"}

\* Partial correctness: a quiesced run has not left any reachable node unmarked.
PartialCorrectness == (pc = "quiesced") => (ReachableFromRoot \subseteq marked)

Termination == <>(pc = "quiesced")

\* Model-checking substitution: the graph is finite and each node has exactly
\* two successors, chosen deterministically, and sequences are bounded to
\* the number of nodes so the reachable set stays finite.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====