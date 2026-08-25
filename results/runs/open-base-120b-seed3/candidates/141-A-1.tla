---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The distinguished root node (Root \\in Nodes)
    Succ            \* Successor function: [Nodes -> SUBSET Nodes]

\*----------------------------------------------------------------------
\* Operators required by the .cfg substitution
\*----------------------------------------------------------------------

ConnectedToSomeButNotAll(n) == Succ[n]

\* LimitedSeq replaces the usual Seq operator from the Sequences module.
LimitedSeq(S) == Seq(S)

\*----------------------------------------------------------------------
\* State variables
\*----------------------------------------------------------------------

VARIABLES
    marked,         \* Set of nodes that have been marked (visited)
    frontier,       \* Set of nodes that are in the frontier (may overlap marked)
    pc              \* Program counter: "Running" or "Done"

\*----------------------------------------------------------------------
\* Helper definition: nodes reachable from a set of sources via the
\* successor relation (any finite number of steps)
\*----------------------------------------------------------------------

ReachableFrom(S) ==
    { t \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) >= 1
            /\ p[1] \in S
            /\ p[Len(p)] = t
            /\ \A i \in 1 .. Len(p)-1 :
                p[i+1] \in ConnectedToSomeButNotAll[p[i]]
    }

\*----------------------------------------------------------------------
\* Initial state
\*----------------------------------------------------------------------

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

\*----------------------------------------------------------------------
\* Main action (nondeterministically pick a node from frontier)
\*----------------------------------------------------------------------

PickNodeAction ==
    /\ frontier # {}
    /\ \E n \in frontier :
        \/ /\ n \\notin marked
           /\ marked' = marked \\cup {n}
           /\ frontier' = frontier \\cup ConnectedToSomeButNotAll[n]
           /\ pc' = pc
        \/ /\ n \\in marked
           /\ marked' = marked
           /\ frontier' = frontier \\ {n}
           /\ pc' = pc

\*----------------------------------------------------------------------
\* Termination action (when frontier becomes empty)
\*----------------------------------------------------------------------

TerminateAction ==
    /\ frontier = {}
    /\ pc = "Running"
    /\ pc' = "Done"
    /\ UNCHANGED << marked, frontier >>

\*----------------------------------------------------------------------
\* Next-state relation
\*----------------------------------------------------------------------

Next ==
    \/ PickNodeAction
    \/ TerminateAction
    \/ /\ pc = "Done"
       /\ UNCHANGED << marked, frontier, pc >>

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*----------------------------------------------------------------------
\* Invariants
\*----------------------------------------------------------------------

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

Inv1 ==
    \A m \in marked :
        ConnectedToSomeButNotAll[m] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup ReachableFrom(frontier)) = ReachableFrom(marked \cup frontier)

Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
    (frontier = {}) => (marked = ReachableFrom({Root}))

\*----------------------------------------------------------------------
\* Liveness property
\*----------------------------------------------------------------------

Termination == <> (frontier = {})

\*----------------------------------------------------------------------
\* THEOREMS (optional, for convenience)
\*----------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====