---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,   \* The set of all graph nodes.
    Root,    \* The root node from which reachability is computed.
    Succ,    \* A function Succ \in [Nodes -> SUBSET Nodes] giving successors.
    Seq      \* A sequence of all nodes in Nodes (used only for a harmless type check).

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    marked,   \* Set of nodes that have been visited.
    frontier, \* Set of nodes that are candidates for exploration (may overlap with marked).
    pc        \* Program counter: either "Loop" (still running) or "Done" (terminated).

\* ----------------------------------------------------------------------
\* Helper definition
ReachableFrom(S) == 
    \* The set of nodes reachable from any node in set S via any number of Succ steps.
    RECURSIVE ReachFrom(_)
    ReachFrom(S) == 
        IF S = {} THEN {}
        ELSE LET s == CHOOSE x \in S: TRUE IN
             {s} \cup ReachFrom(S \ {s} \cup Succ[s])

\* For readability we also define the set of nodes reachable from the Root.
ReachRoot == ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Loop"

\* ----------------------------------------------------------------------
\* Actions
PickFrontier == 
    \* Choose a nondeterministic node from the current frontier.
    CHOOSE n \in frontier : TRUE

Explore ==
    /\ pc = "Loop"
    /\ \E n \in frontier :
        /\ IF n \notin marked THEN
               /\ marked'   = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
           ELSE
               /\ marked'   = marked
               /\ frontier' = frontier \ {n}
        /\ pc' = "Loop"

Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ Explore
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Safety invariants described in the natural-language description

\* Inv1: Every successor of a marked node is either already marked or in the frontier.
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: The union of marked nodes and the nodes reachable from the frontier 
\*       equals the nodes reachable from the union of marked and frontier.
Inv2 ==
    ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)

\* Inv3: The set of nodes reachable from the root equals the marked set plus the nodes
\*       reachable from the frontier.
Inv3 ==
    ReachRoot = marked \cup ReachFrom(frontier)

\* PartialCorrectness: When the algorithm has terminated, marked equals exactly
\* the set of nodes reachable from the root.
PartialCorrectness ==
    pc = "Done" => marked = ReachRoot

\* ----------------------------------------------------------------------
\* Liveness property (termination under finiteness of reachable set)
Termination ==
    WF_vars(Explore)

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the module self‑contained)
THEOREM TypeOK => Init /\ [][Next]_<<marked, frontier, pc>>

=============================================================================