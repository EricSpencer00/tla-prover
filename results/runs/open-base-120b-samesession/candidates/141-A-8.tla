---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANTS
    Nodes,            \* The set of all graph nodes
    Root,             \* The distinguished root node
    Succ               \* Successor function: [node -> SUBSET Nodes]

\*-----------------------------------------------------------------
\* Operators overridden by the .cfg file
\*-----------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*-----------------------------------------------------------------
\* A finite version of Seq for model checking
\*-----------------------------------------------------------------
MAXLEN == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MAXLEN }

\*-----------------------------------------------------------------
\* Reachability definition (finite paths)
\*-----------------------------------------------------------------
Reach(S) ==
    { n \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) >= 1
            /\ p[1] \in S
            /\ p[Len(p)] = n
            /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]
    }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES marked, frontier, pc

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"run", "done"}

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ Root \in Nodes

\*-----------------------------------------------------------------
\* Main algorithm actions
\*-----------------------------------------------------------------
Explore ==
    /\ pc = "run"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = pc
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = pc
        /\ UNCHANGED << >>   \* no other variables change

Terminate ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ Terminate
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = Reach({Root})

\*-----------------------------------------------------------------
\* Liveness property (termination)
\*-----------------------------------------------------------------
Termination == <> (pc = "done")

=============================================================================