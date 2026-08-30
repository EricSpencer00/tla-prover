---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* A directed graph is given as a constant successor relation. Misra's
\* variant of BFS lets the marked and frontier sets overlap, which is what
\* the reachable-from-frontier invariant below is there to keep sound.
CONSTANTS Nodes, Root, Succ

RangeOf(f, S) == {f[x] : x \in S}

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "halted"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The two cases are the same action with a nondeterministic choice
\* inside it; that is what lets TLC allocate the two fairness shares.
Explore ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ IF n \notin marked
           THEN /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup RangeOf(Succ, {n})
           ELSE /\ marked' = marked
                /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier = {} THEN "halted" ELSE "running"

Next == Explore

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

SuccessorReachable(n) == {m \in Nodes : \E k \in Nat : Len(LimitedSeq(Succ, n, k)) >= 1 /\ LimitedSeq(Succ, n, k)[Len(LimitedSeq(Succ, n, k))] = m}

FromRoot == SuccessorReachable(Root)

FiniteReach == Cardinality(FromRoot) < Cardinality(Nodes)

\* Every successor of a marked node is either already marked or still in
\* flight in the frontier -- with no overlap elimination, that is not
\* the same as saying frontier nodes are unmarked, and it is the shared
\* foundation of the other two invariants below.
Inv1 == \A n \in marked : SuccessorReachable(n) \subseteq (marked \cup frontier)

FromFrontier == UNION {SuccessorReachable(n) : n \in frontier}

\* Marked nodes are closed under the graph's reachability relation, so
\* everything reachable from the current marked-and-frontier union is
\* already accounted for in the marked set.
Inv2 == (marked \cup FromFrontier) = SuccessorReachable(marked \cup frontier)

Inv3 == FromRoot = (marked \cup FromFrontier)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == FiniteReach ~> (pc = "halted")

====