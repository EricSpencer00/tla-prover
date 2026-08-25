---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operator that will be substituted for Succ in the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Finite version of Seq (replaces Seq via LimitedSeq)
\* ----------------------------------------------------------------------
LimitedSeq == Seq(Nodes)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
R == [n \in Nodes |-> ConnectedToSomeButNotAll(n)]

Identity == { <<n, n>> : n \in Nodes }

Reach(S) == { y \in Nodes :
               \E x \in S : <<x, y>> \in (TC(R) \cup Identity) }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            ( /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
               /\ pc' = pc
            )
            \/ ( /\ n \in marked
                 /\ marked' = marked
                 /\ frontier' = frontier \setminus {n}
                 /\ pc' = pc
               )
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is in marked \/ frontier
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked :
           ConnectedToSomeButNotAll(n) \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: union of marked and reachable from frontier equals
\* reachable from marked ∪ frontier
\* ----------------------------------------------------------------------
Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: reachable from root equals marked ∪ reachable from frontier
\* ----------------------------------------------------------------------
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked equals the set of nodes
\* reachable from the root
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====