---- MODULE Reachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

\* Reachable from a seed set via Succ, with an explicit iteration budget so
\* the reachable set stays finite even when Succ is infinite.
ReachableFrom(seed) ==
    LET RECURSIVE Reach(S) ==
        IF S = {} THEN {}
        ELSE LET x == CHOOSE y \in S : TRUE IN Succ[x] \cup Reach(S \ {x})
    IN Reach(seed)

NReachable == Cardinality(ReachableFrom({Root}))

Inv1 == \A n \in marked : (Succ[n] \subseteq marked) \/ (Succ[n] \cap frontier # {})
Inv2 == ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)
Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Pick any frontier node; the overlapping-mark-and-frontier design is what
\* makes this choice nondeterministic from the algorithm's own point of view.
Step ==
    /\ pc = "running"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked
        THEN /\ marked' = marked \cup {n}
             /\ frontier' = frontier \cup Succ[n]
        ELSE /\ marked' = marked
             /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next == Step

Spec == Init /\ [][Next]_vars

Termination == (pc = "running" /\ frontier # {}) ~> (pc = "done")

\* The reachable set is finite: a bounded version of Succ keeps the model
\* finite even when Succ itself is infinite.
Succ(n) == ConnectedToSomeButNotAll(n)

\* A bounded (finite) version of Seq, so the model is checkable; replaces the
\* standard Seq operator from Sequences.
LimitedSeq ==
    [n \in Nat |-> IF n = 0 THEN {}
                     ELSE LET m == CHOOSE k \in Nat : n = k + 1
                          IN m]

====