---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Inv1 ==
    \A x \in marked : Succ[x] \subseteq marked \cup frontier

Inv2 ==
    ReachableFrom(frontier) \cup marked = ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    /\ (pc = "done") => (marked = ReachableFrom({Root}))
    /\ Inv1 /\ Inv2 /\ Inv3

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

Explore ==
    /\ frontier # {}
    /\ \E x \in frontier :
         IF x \notin marked
         THEN /\ marked' = marked \cup {x}
              /\ frontier' = frontier \cup Succ[x]
         ELSE /\ frontier' = frontier \ {x}
              /\ UNCHANGED marked
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)

Termination == Termination == (pc = "done")
              /\ (Cardinality(ReachableFrom({Root})) < \infinity => (pc = "done"))

\* Finite version of Seq for the .cfg's operator substitution.
LimitedSeq(S, n) == {s \in Seq(S) : Len(s) <= n}

RECURSIVE ReachableFrom(_)
ReachableFrom(T) ==
    IF T = {} THEN {}
    ELSE LET x == CHOOSE y \in T : TRUE
         IN Succ[x] \cup ReachableFrom(T \ {x})

=============================================================================