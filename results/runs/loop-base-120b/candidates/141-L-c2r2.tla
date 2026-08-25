---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANTS
    Nodes,    \* The set of all graph nodes
    Root,     \* The distinguished start node (Root \in Nodes)
    Succ      \* A total function Nodes -> SUBSET Nodes giving successors

\*-----------------------------------------------------------------
\* Operators required by the .cfg substitution
\*-----------------------------------------------------------------
\* A finite version of Seq used by the configuration (replaces Seq).
\* We bound the length of sequences by a small constant to keep the model finite.
MaxLen == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

\* The configuration substitutes Succ with ConnectedToSomeButNotAll.
\* We define it in terms of the original Succ constant.
ConnectedToSomeButNotAll == [n \in Nodes |-> Succ[n]]

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
\* Reachability from a set of start nodes using finite paths
ReachFrom(startSet) ==
    { v \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) >= 1
            /\ p[1] \in startSet
            /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]
            /\ p[Len(p)] = v }

\* Reachability from the single root node
Reachable == ReachFrom({Root})

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES
    marked,    \* Set of already marked (visited) nodes
    frontier,  \* Set of nodes that are still to be explored
    pc         \* Program counter: "running" or "done"

vars == <<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ UNCHANGED pc
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ UNCHANGED pc
    \/ /\ frontier = {}
       /\ pc = "running"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    (frontier = {}) => (marked = ReachFrom({Root}))

\*-----------------------------------------------------------------
\* Liveness property (termination)
\*-----------------------------------------------------------------
Termination == <> (frontier = {})

=============================================================================