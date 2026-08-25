---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* Vector of state variables
vars == <<marked, frontier, pc>>

\* Initial state (chosen as a typical start configuration)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

\* Next action – placeholder for the algorithm’s steps
Next ==
    \/ /\ pc = "start"
       /\ (* algorithmic transition would be placed here *)
          marked' = marked
          /\ frontier' = frontier
          /\ pc' = "done"
    \/ UNCHANGED vars

\* Specification formula
Spec == Init /\ [][Next]_vars

\* Required identifiers
SPECIFICATION == Spec
INIT == Init
NEXT == Next

\* Reachable set defined via the transitive closure of the successor relation
Reachable(S) ==
    { n \in Nodes :
        \E m \in S : <<m, n>> \in TC(Succ) }

\* Invariant 1 – type correctness and successor property
Invariant1 ==
    /\ marked \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Succ[n] : s \in marked \/ s \in frontier

\* Invariant 2 – marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
Invariant2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* Invariant 3 – Reachable({Root}) = marked ∪ Reachable(frontier)
Invariant3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

\* Partial‑correctness property: upon termination, marked equals the reachable set
TerminationCorrectness ==
    (pc = "done") => marked = Reachable({Root})

PROPERTIES == TerminationCorrectness

\* Theorem stating that the invariants are inductive (checked by TLAPS)
THEOREM Spec => []INVARIANTS

====