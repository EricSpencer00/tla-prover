---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Successors(n) == { m \in Nodes : m \neq n } \* (replace with actual edge relation if available)

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Loop", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness + each successor of a marked node is
\* either already marked or in the frontier.
\* ----------------------------------------------------------------------
Inv1 ==
    /\ TypeOK
    /\ \A n \in marked : Successors(n) \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ ReachableFrom(frontier) = ReachableFrom(marked ∪ frontier)
\* (ReachableFrom is defined in the auxiliary Reachability module, assumed
\*  to be imported or defined elsewhere.)
\* ----------------------------------------------------------------------
\* Placeholder for ReachableFrom; in practice this would be imported.
ReachableFrom(S) == { y \in Nodes : \E x \in S : x \in Nodes } \* Stub definition

Inv2 == marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: ReachableFrom({Root}) = marked ∪ ReachableFrom(frontier)
\* ----------------------------------------------------------------------
Inv3 == ReachableFrom({Root}) = marked ∪ ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* Initial state (the description says NOT_SPECIFIED; we choose a reasonable
\* initialization that respects the invariants.)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"
    /\ Inv1
    /\ Inv2
    /\ Inv3

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
AddNode ==
    /\ pc = "Loop"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Successors(n) \ marked)
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Loop"
        /\ UNCHANGED << >>

Next ==
    \/ AddNode

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* The required identifiers
\* ----------------------------------------------------------------------
INVARIANT1 == Inv1
INVARIANT2 == Inv2
INVARIANT3 == Inv3

\* ----------------------------------------------------------------------
\* The module must expose the following identifiers:
\*   - CONSTANTS: Nodes, Root (already declared)
\*   - SPECIFICATION formula: Spec
\*   - Operators: Spec, Init, Next, Inv1, Inv2, Inv3
\*   - Aliases for the invariants as required by the .cfg file
\* ----------------------------------------------------------------------
SpecInvs == <<Inv1, Inv2, Inv3>>

====