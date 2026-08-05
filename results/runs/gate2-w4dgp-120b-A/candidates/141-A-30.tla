---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"looping", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "looping"

\* Misra's BFS variant: the frontier and the visited set may overlap, which
\* simplifies parallel processing. Picking is nondeterministic.
ExploreStep ==
    /\ pc = "looping"
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
           /\ marked' = marked
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "looping"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == ExploreStep \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(ExploreStep)

\* Safety invariants for partial correctness: frontier retains the right
\* connecting invariant even though it overlaps with marked.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 == Reachable(Nodes, frontier) \cup marked = Reachable(Nodes, marked \cup frontier)
Inv3 == Reachable(Nodes, {Root}) = marked \cup Reachable(Nodes, frontier)
PartialCorrectness == pc = "done" => Reachable(Nodes, {Root}) = marked

Termination == Reachable(Nodes, {Root}) # Nodes => <>(pc = "done")

\* Bounded projection of the infinite Reachable definition, used in the model
\* instead of the full successor relation to stay inside a finite universe.
ConnectedToSomeButNotAll(n) == Succ[n] \ {n}

\* Bounded version of Seq (inherited from Sequences, overridden in the .cfg)
LimitedSeq(S) == { seq \in Seq(S) : Len(seq) <= 3 }

====