---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be supplied in the .cfg file)
\*   Nodes  : the set of all graph nodes
\*   Root   : the designated start node, assumed to be in Nodes
\*   Succ   : successor relation, a function Nodes -> SUBSET Nodes
\*   Seq    : the natural numbers (used for the program counter)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables
\*   marked   : set of nodes that have been visited
\*   frontier : set of nodes that are candidates for exploration
\*   pc       : program counter, either "Loop" or "Done"
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\*   ReachableFrom(S) – the set of nodes reachable from any node in S
\* ----------------------------------------------------------------------
ReachableFrom(S) == 
    CHOOSE T \in SUBSET Nodes :
        /\ S \subseteq T
        /\ \A n \in T : Succ[n] \subseteq T
        /\ \A U \in SUBSET Nodes :
              (S \subseteq U /\ \A n \in U : Succ[n] \subseteq U) => T \subseteq U

\* The above definition captures the least fixed point of the successor
\* operator containing S. In practice, TLC will evaluate it by enumerating
\* subsets of Nodes (which must be finite in the model).

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
DoStep ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = pc
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED << marked, frontier >>

Next ==
    \/ DoStep
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Safety invariants described in the natural-language text
\* ----------------------------------------------------------------------
\* Inv1: Every successor of a marked node is either already marked
\*       or still in the frontier.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: The union of the marked set and the set reachable from the frontier
\*       equals the set reachable from the union of marked and frontier.
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Inv3: The set of nodes reachable from the root equals the marked set
\*       plus the nodes reachable from the frontier.
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* PartialCorrectness: When the algorithm has terminated, the marked set
\* equals exactly the set of nodes reachable from the root.
PartialCorrectness ==
    pc = "Done" => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination) – placed in the PROPERTIES list
\* ----------------------------------------------------------------------
Termination ==
    []<>(pc = "Done")

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep them for completeness)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====