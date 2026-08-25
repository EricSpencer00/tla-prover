---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,               \* the set of all graph nodes
    Root,                \* a distinguished node in Nodes
    Succ                 \* successor function: Nodes -> SUBSET Nodes

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Relation version of Succ, used for reachability via transitive closure
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Reachable nodes from a set S (reflexive transitive closure of SuccRel)
Reach(S) == { n \in Nodes : 
                \E s \in S : <<s, n>> \in (SuccRel)^* }

\* A finite version of Seq (bounded length 10, arbitrary choice)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 10 }

\* Operator that will be substituted for Succ by the .cfg file
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    marked,   \* set of nodes already marked (visited)
    frontier, \* set of nodes pending exploration (may overlap with marked)
    pc        \* program counter: "Running" or "Done"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ pc' = IF frontier \cup Succ[n] = {} THEN "Done" ELSE "Running"
    \/ \E n \in frontier :
          /\ n \in marked
          /\ marked' = marked
          /\ frontier' = frontier \ {n}
          /\ pc' = IF frontier \ {n} = {} THEN "Done" ELSE "Running"

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Invariants required for partial correctness
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    pc = "Done" => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination ==
    <> (frontier = {})

\* ----------------------------------------------------------------------
\* Theorem declarations (so TLC can check them)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====