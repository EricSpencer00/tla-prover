---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Nodes,      \* the set of all graph nodes
    Root,       \* a distinguished start node, Root \\in Nodes
    Succ        \* successor function: Nodes -> SUBSET Nodes

\* ----------------------------------------------------------------------
\* Operators substituted by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == 
    [n \\in Nodes |-> {}]   \* placeholder: no edges (to be overridden in the cfg)

LimitedSeq(S) == 
    /\ Seq(S)
    /\ Len(S) <= 10          \* finite bound for model checking

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    marked,      \* set of nodes that have been visited
    frontier,    \* set of nodes awaiting exploration (may overlap with marked)
    pc           \* program counter: "run" or "done"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Reachable(S) returns the set of nodes reachable from any node in S
RECURSIVE Reachable(_)
Reachable(S) ==
    S \/ { y \\in Nodes : \\E x \\in Reachable(S) : y \\in Succ[x] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Process ==
    /\ pc = "run"
    /\ frontier # {}
    /\ LET n == CHOOSE v \\in frontier IN
       IF n \\notin marked THEN
          /\ marked' = marked \\cup {n}
          /\ frontier' = frontier \\cup Succ[n]
          /\ UNCHANGED pc
       ELSE
          /\ marked' = marked
          /\ frontier' = frontier \\ {n}
          /\ UNCHANGED pc
    /\ UNCHANGED << >>   \* no other variables

Terminate ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Next ==
    Process \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \\subseteq Nodes
    /\ frontier \\subseteq Nodes
    /\ pc \\in {"run", "done"}

Inv1 ==
    /\ \\A n \\in marked : Succ[n] \\subseteq marked \\cup frontier

Inv2 ==
    /\ marked \\cup Reachable(frontier) = Reachable(marked \\cup frontier)

Inv3 ==
    /\ Reachable({Root}) = marked \\cup Reachable(frontier)

PartialCorrectness ==
    /\ pc = "done" => marked = Reachable({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination ==
    <> (pc = "done")

\* ----------------------------------------------------------------------
\* Theorems (optional, to expose the invariants to TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====