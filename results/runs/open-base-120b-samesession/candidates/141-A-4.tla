---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Nodes,          \* the set of all graph nodes
    Root,           \* the root node (must be in Nodes)
    Succ,           \* function mapping each node to its successors
    MaxSeqLen       \* bound for LimitedSeq

VARIABLES
    marked,         \* set of visited (marked) nodes
    frontier,       \* set of nodes awaiting exploration
    pc              \* program counter: "Run" or "Done"

\* ----------------------------------------------------------------------
\* Operator that the .cfg substitutes for Succ
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq used for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Edge relation derived from the successor function
Edge == [n \in Nodes, m \in Nodes] |-> m \in ConnectedToSomeButNotAll(n)

\* Reachability from a set of source nodes using transitive closure
ReachFrom(S) == { y \in Nodes :
                    \E x \in S : <<Edge>>^* (x, y) }

\* Reachable nodes from the root
ReachRoot == ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* Main step: pick a node from the frontier and process it
ChooseAction ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ IF n \notin marked THEN
                 /\ marked'   = marked \cup {n}
                 /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
             ELSE
                 /\ marked'   = marked
                 /\ frontier' = frontier \ {n}
          /\ pc' = "Run"

\* Termination step when the frontier becomes empty
Terminate ==
    /\ pc = "Run"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next == ChooseAction \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachRoot = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    frontier = {} => marked = ReachRoot

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg
THEOREM SpecIsSpec == Spec

====