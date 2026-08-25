---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* Constants required by the configuration
\*--------------------------------------------------------------------
CONSTANTS
    Nodes,    \* The finite set of nodes (e.g., 1..4)
    Root,     \* The start node
    Succ      \* Will be overridden by ConnectedToSomeButNotAll in the .cfg

\*--------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq)
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*--------------------------------------------------------------------
\* Concrete successor relation (overrides Succ)
\*--------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    CASE n = 1 -> {2,3}
    []  n = 2 -> {3,4}
    []  n = 3 -> {1,4}
    []  n = 4 -> {1,2}
    []  OTHER -> {}

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES
    marked,   \* Set of nodes already discovered
    frontier, \* Set of nodes to be explored next
    pc        \* Program counter (either "run" or "done")

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
IsDone == frontier = {}

\* Reachable nodes from Root using bounded paths
Reachable ==
    { n \in Nodes :
        \E p \in LimitedSeq(Nodes) :
            /\ Len(p) > 0
            /\ p[1] = Root
            /\ p[Len(p)] = n
            /\ \A i \in 1 .. Len(p)-1 :
                 p[i+1] \in ConnectedToSomeButNotAll(p[i])
    }

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\*--------------------------------------------------------------------
\* One step of the sequential reachability algorithm
\*--------------------------------------------------------------------
Next ==
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup
                           (ConnectedToSomeButNotAll(n) \ marked)
            /\ pc' = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "run"
       /\ frontier = {}
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==   \* Successor closure: successors of marked nodes are in marked ∪ frontier
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

Inv2 ==   \* All explored nodes are either marked or in frontier
    marked \cup frontier \subseteq Nodes

Inv3 ==   \* The set of marked nodes equals the set of nodes reachable from Root
    marked = Reachable

PartialCorrectness ==
    IsDone => marked = Reachable

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> IsDone

=============================================================================