---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----- Constants (to be instantiated in the .cfg) -----
CONSTANTS
    Nodes,      \* Set of node identifiers
    Root,       \* The distinguished start node
    Succ,       \* Function: Nodes -> SUBSET Nodes (the outgoing edges)
    Seq         \* Upper bound on the length of any path (a natural number)

\* ----- State variables (inherited from the sequential reachability algorithm) -----
VARIABLES
    marked,     \* The set of nodes that have been discovered
    frontier,   \* The set of nodes whose successors still need to be explored
    pc          \* Program counter representing the current phase of the algorithm

\* ----- Derived values -----
\* The set of all possible nodes for readability
NodeSet == Nodes

\* ----- Initial state (Spec inherits the algorithm's INIT) -----
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "Explore"

\* ----- Next-state relation (Spec inherits the algorithm's NEXT) -----
ExploreStep ==
    /\ frontier # {}
    /\ LET n == CHOOSE x \in frontier : TRUE
       IN /\ marked' = marked \cup Succ[n]
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
    /\ pc' = "Explore"

Terminate ==
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ ExploreStep
    \/ Terminate

\* ----- Specification -----
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----- Invariants -----
TypeOK ==
    /\ marked \subseteq NodeSet
    /\ frontier \subseteq NodeSet
    /\ pc \in {"Explore", "Done"}

\* Inv1: Successor closure – every node in `marked` has all its successors also in `marked` or in `frontier`.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: Reachability decomposition – any node not in `marked` is not reachable from any node in `marked` via a path of length ≤ Seq.
Inv2 ==
    \A n \in NodeSet \ marked :
        \A m \in marked :
            \A p \in 1..Seq :
                ~(\E s \in Seq(1..p) :
                      /\ Len(s) = p
                      /\ s[1] = m
                      /\ s[p] = n
                      /\ \A i \in 1..p-1 : s[i+1] \in Succ[s[i]])

\* Inv3: Reachable set equality – the set `marked` equals the set of nodes reachable from `Root` within `Seq` steps.
ReachableFromRoot(d) ==
    { n \in NodeSet :
        \E p \in 1..d :
            \E s \in Seq(1..p) :
                /\ Len(s) = p
                /\ s[1] = Root
                /\ s[p] = n
                /\ \A i \in 1..p-1 : s[i+1] \in Succ[s[i]] }

Inv3 == marked = ReachableFromRoot(Seq)

\* PartialCorrectness – when the algorithm is done, `marked` is exactly the set of all nodes reachable from `Root`.
PartialCorrectness ==
    pc = "Done" => marked = ReachableFromRoot(Seq)

\* ----- Liveness property -----
Termination == []<>(pc = "Done")

\* ----- Theorems to expose the identifiers for the .cfg -----
THEOREM SpecIsSpec == Spec
THEOREM TypeOKInv == TypeOK
THEOREM Inv1IsInv1 == Inv1
THEOREM Inv2IsInv2 == Inv2
THEOREM Inv3IsInv3 == Inv3
THEOREM PCorrectness == PartialCorrectness
THEOREM TerminationProp == Termination

====