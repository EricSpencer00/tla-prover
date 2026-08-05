---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Marking == [node |-> Root, succes |-> {}]

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"looping", "done"}

INIT ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "looping"

Explore(n) ==
    /\ pc = "looping"
    /\ n \in frontier
    /\ IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = "looping"

Terminate ==
    /\ pc = "looping"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

NEXT == \E n \in Nodes : Explore(n) \/ Terminate

\* Misra's variant lets the visited and frontier sets overlap, so the
\* algorithm's progress comes from shrinking the frontier or growing the
\* visited set, never from both staying still forever.
Spec == Init /\ [][Next]_vars

Inv1 == \A x \in marked : Succ[x] \subseteq (marked \cup frontier)
Inv2 == (marked \cup frontier) \in ConnectedToSomeButNotAll(Nodes, Root)
Inv3 == ReachableFrom(Nodes, Root) = (marked \cup ReachableFrom(frontier, Root))
PartialCorrectness == pc = "done" => marked = ReachableFrom(Nodes, Root)

\* If the reachable set is finite, the frontier eventually empties.
Termination == Cardinality(ReachableFrom(Nodes, Root)) < Nat : <>(frontier = {})

\* A reachable-from-Nodes-and-Root invariant over sets, not sequences
ReachableFrom(T, r) == {r} \cup (UNION {Succ[x] : x \in T})
\* A reachable-to-some-but-not-all invariant over sets, not sequences
ConnectedToSomeButNotAll(T, r) ==
    LET F[S \in SUBSET T] ==
        {\cup {Succ[x] : x \in S}} \cup {r}
    IN {F[S] : S \in SUBSET T}

\* A finite-version replacement for the standard Seq operator, required by
\* the .cfg's substitution of LimitedSeq for Seq (Infinity would be
\* uncheckable in the bounded model the .cfg runs).
LimitedSeq == CHOOSE s \in Seq(Nodes) : Cardinality(s) = 0

====