---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*=====================================================================
\* Constants
\*=====================================================================
CONSTANTS 
    Nodes,       \* The set of all graph nodes
    Root,        \* The distinguished root node
    Succ         \* Successor function: [Nodes -> SUBSET Nodes]

\*=====================================================================
\* Assumptions about the constants
\*=====================================================================
ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

\*=====================================================================
\* Operators substituted by the .cfg file
\*=====================================================================
ConnectedToSomeButNotAll(n) == Succ[n]   \*  used in place of Succ

\*=====================================================================
\* A finite version of Seq for model checking
\*=====================================================================
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= 5 }

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

\*=====================================================================
\* Helper definitions
\*=====================================================================
\* Relation representing graph edges
Rel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

\* Reachability from a set of nodes (reflexive transitive closure)
Reach(S) == { n \in Nodes : \E m \in S : <<m, n>> \in Rel^* }

\*=====================================================================
\* Initialization
\*=====================================================================
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\*=====================================================================
\* Main action (pick a node from the frontier)
\*=====================================================================
ChooseNode ==
    \E n \in frontier :
        /\ IF n \\notin marked THEN
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
           ELSE
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
        /\ pc' = pc

\*=====================================================================
\* Termination action
\*=====================================================================
Terminate ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next == ChooseNode \/ Terminate

\*=====================================================================
\* Specification
\*=====================================================================
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(ChooseNode)

\*=====================================================================
\* Invariants
\*=====================================================================
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (pc = "done") => (marked = Reach({Root}))

\*=====================================================================
\* Liveness property
\*=====================================================================
Termination == <> (pc = "done")

\*=====================================================================
\* Export the required identifiers
\*=====================================================================
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====