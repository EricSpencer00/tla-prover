---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

\*-----------------------------------------------------------------
\* Constants required by the configuration
\*-----------------------------------------------------------------
CONSTANTS Nodes, Root, Succ

\*-----------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------
VARIABLES marked, frontier, pc

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

\*-----------------------------------------------------------------
\* Reachability operator (transitive closure of Succ)
\*-----------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE
        LET next == UNION { Succ[n] : n \in S } IN
        S \cup Reach(next \ S)

\*-----------------------------------------------------------------
\* Invariants described in the specification
\*-----------------------------------------------------------------
Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    pc = "done" => marked = Reach({Root})

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\*-----------------------------------------------------------------
\* Main step of the algorithm
\*-----------------------------------------------------------------
Next ==
    \/ /\ pc = "running"
       /\ frontier # {}
       /\ \E n \in frontier:
            /\ IF n \notin marked THEN
                   /\ marked' = marked \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
               ELSE
                   /\ marked' = marked
                   /\ frontier' = frontier \ {n}
            /\ pc' = IF frontier' = {} THEN "done" ELSE "running"
            /\ UNCHANGED << >>
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Property: eventual termination
\*-----------------------------------------------------------------
Termination == <> (pc = "done")
====