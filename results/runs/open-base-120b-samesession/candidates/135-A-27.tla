---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Configuration specific operator: a bounded version of the successor
\* relation.  The .cfg will substitute this for the identifier Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Bounded version of Seq for model checking (replaces Seq via .cfg)
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state (inherited, instantiated with concrete graph)
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Init"

\* ----------------------------------------------------------------------
\* Next-state relation (standard reachability algorithm)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Init"
       /\ pc' = "Step"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ /\ pc = "Step"
       /\ \E n \in Frontier :
            /\ Marked' = Marked \cup {n}
            /\ Frontier' = (Frontier \cup ConnectedToSomeButNotAll[n]) \ {n}
            /\ pc' = IF ( (Frontier \cup ConnectedToSomeButNotAll[n]) \ {n} = {} )
                     THEN "Done"
                     ELSE "Step"

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Helper definition of reachable nodes via bounded sequences
\* ----------------------------------------------------------------------
Reachable ==
    { n \in Nodes :
        \E s \in LimitedSeq :
            /\ Len(s) >= 1
            /\ Head(s) = Root
            /\ Last(s) = n
            /\ \A i \in 1 .. (Len(s) - 1) :
                 s[i+1] \in ConnectedToSomeButNotAll[s[i]]
    }

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}

Inv1 == \A n \in Marked : ConnectedToSomeButNotAll[n] \subseteq Marked

Inv2 == \A n \in Frontier : n \notin Marked

Inv3 == Marked = Reachable

PartialCorrectness ==
    (pc = "Done") => (Marked = Reachable)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====