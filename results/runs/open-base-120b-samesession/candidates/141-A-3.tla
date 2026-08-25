---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Nodes,      \* The set of all graph nodes
    Root,       \* The distinguished start node (Root \\in Nodes)
    Succ        \* Successor function: Succ[n] \\subseteq Nodes

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Relation induced by the successor function
Rel == { <<n, m>> : n \\in Nodes \\land m \\in Succ[n] }

\* Nodes reachable (in zero or more steps) from a set S
Reach(S) == 
    LET TC == TC(Rel) IN
    S \\cup { y \\in Nodes : \\E x \\in S : <<x, y>> \\in TC }

\* Finite version of Seq for model checking
CONSTANT MaxSeqLen
LimitedSeq(S) == { s \\in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* Action when a node from the frontier is not yet marked
MarkAndAdd(node) ==
    /\ node \\in frontier
    /\ node \\notin marked
    /\ marked' = marked \\cup {node}
    /\ frontier' = frontier \\cup Succ[node]
    /\ pc' = pc

\* Action when a node from the frontier is already marked
Remove(node) ==
    /\ node \\in frontier
    /\ node \\in marked
    /\ marked' = marked
    /\ frontier' = frontier \\ {node}
    /\ pc' = IF frontier' = {} THEN "Done" ELSE pc

\* The main nondeterministic step
Next ==
    \\E node \\in frontier :
        ( MarkAndAdd(node) \/ Remove(node) )

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \\subseteq Nodes
    /\ frontier \\subseteq Nodes
    /\ pc \\in {"Run", "Done"}

Inv1 ==
    /\ \\A n \\in marked : Succ[n] \\subseteq marked \\cup frontier

Inv2 ==
    /\ marked \\cup Reach(frontier) = Reach(marked \\cup frontier)

Inv3 ==
    /\ Reach({Root}) = marked \\cup Reach(frontier)

PartialCorrectness ==
    /\ frontier = {} => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* Operators required by the .cfg substitution
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]  \* placeholder; the .cfg will replace Succ with this

\* ----------------------------------------------------------------------
\* THEOREMS (optional, can be used by the model checker)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====