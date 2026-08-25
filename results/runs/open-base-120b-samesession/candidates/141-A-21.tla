---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Fairness

CONSTANTS
    Nodes,      \* the set of all graph nodes
    Root,       \* a distinguished node in Nodes
    Succ        \* a function Nodes -> SUBSET Nodes giving successors

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) == 
    LET
        R == TC(SuccRel)               \* transitive closure of the successor relation
    IN
        S \cup { n \in Nodes : \E s \in S : <<s, n>> \in R }

\* ----------------------------------------------------------------------
\* Bounded version of Seq (required by the .cfg)
\* ----------------------------------------------------------------------
CONSTANT MaxLen
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= MaxLen }

\* ----------------------------------------------------------------------
\* Operator to be substituted for Succ in the .cfg (provided here)
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: successors of marked nodes are either marked or in frontier
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
\* ----------------------------------------------------------------------
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked = Reach({Root})
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "done") => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init == 
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Main exploration action
\* ----------------------------------------------------------------------
Explore == 
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "run"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "run"

\* ----------------------------------------------------------------------
\* Termination action
\* ----------------------------------------------------------------------
Terminate == 
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Explore \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Explore)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
\* The spec name
Spec == Spec

\* The invariants
TypeOK == TypeOK
Inv1 == Inv1
Inv2 == Inv2
Inv3 == Inv3
PartialCorrectness == PartialCorrectness

\* The property
Termination == Termination

====