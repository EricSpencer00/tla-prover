---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be provided in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Nodes,          \* Set of all graph nodes
    Root,           \* Root node, must be in Nodes
    Succ,           \* Succ is a function [Nodes -> SUBSET Nodes] giving successors
    Seq             \* Not used directly in this module but required by cfg

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    marked,         \* Set of nodes that have been visited
    frontier,       \* Set of nodes pending exploration (may overlap with marked)
    pc              \* Program counter: "Running" or "Done"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NodeSet == Nodes

AllMarkedReachable == { n \in NodeSet : 
    \E p \in Seq: p[1] = Root /\ 
                 \A i \in 1..(Len(p)-1): p[i+1] \in Succ[p[i]] /\ 
                 p[Len(p)] = n }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"
    /\ Root \in NodeSet

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
PickFromFrontier == 
    \E x \in frontier :
        \/ /\ x \notin marked
           /\ marked' = marked \cup {x}
           /\ frontier' = frontier \cup Succ[x]
           /\ pc' = "Running"
        \/ /\ x \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {x}
           /\ pc' = "Running"

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ /\ pc = "Running" /\ frontier # {}
       /\ PickFromFrontier
    \/ /\ pc = "Running" /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is in marked or frontier
\* ----------------------------------------------------------------------
Inv1 ==
    \A v \in marked : Succ[v] \subseteq (marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 2: union of marked and nodes reachable from frontier equals
\*            nodes reachable from marked ∪ frontier
\* ----------------------------------------------------------------------
ReachFrom(S) ==
    { n \in NodeSet :
        \E p \in Seq :
            /\ Len(p) >= 1
            /\ p[1] \in S
            /\ \A i \in 1..(Len(p)-1) : p[i+1] \in Succ[p[i]]
            /\ p[Len(p)] = n }

Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: nodes reachable from root equal marked plus nodes reachable
\*            from frontier
\* ----------------------------------------------------------------------
Inv3 ==
    AllMarkedReachable = marked \cup ReachFrom(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked equals exactly the reachable set
\* ----------------------------------------------------------------------
PartialCorrectness ==
    pc = "Done" => marked = AllMarkedReachable

\* ----------------------------------------------------------------------
\* Liveness property: termination when reachable set is finite
\* (expressed as a weak fairness property on Next)
\* ----------------------------------------------------------------------
Termination ==
    WF_vars(Next)

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by cfg but useful for sanity)
\* ----------------------------------------------------------------------
THEOREM Spec => []PartialCorrectness

====