---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,        \* the set of all graph nodes
    Root,         \* the distinguished root node (Root \in Nodes)
    Succ          \* a total function mapping each node to the set of its successors

\* ----------------------------------------------------------------------
\*  Operators required by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S)   \* a finite version of Seq (Seq already yields finite sequences)

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES
    marked,        \* set of nodes that have been visited
    frontier,      \* set of nodes pending exploration (may overlap with marked)
    pc             \* program counter: "Run" or "Done"

vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\*  Reachability definition (transitive closure of ConnectedToSomeButNotAll)
\* ----------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE
        LET step == { y \in Nodes : \E n \in S : y \in ConnectedToSomeButNotAll(n) } 
        IN  S \cup Reach(step)

\* ----------------------------------------------------------------------
\*  Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\*  Main actions
\* ----------------------------------------------------------------------
Pick ==
    \E n \in frontier :
        /\ IF n \notin marked THEN
               /\ marked'   = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
           ELSE
               /\ marked'   = marked
               /\ frontier' = frontier \ {n}
        /\ pc' = pc
        /\ UNCHANGED << >>

Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ marked'   = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

Next ==
    Pick \/ Terminate

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

Inv2 ==
    Reach(marked \cup frontier) = marked \cup Reach(frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    pc = "Done" => marked = Reach({Root})

\* ----------------------------------------------------------------------
\*  Liveness property
\* ----------------------------------------------------------------------
Termination ==
    <> (pc = "Done")

=============================================================================