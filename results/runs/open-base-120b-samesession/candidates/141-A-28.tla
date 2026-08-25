---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) == 
  S \cup { m \in Nodes : \E n \in S : <<n, m>> \in TC(SuccRel) }

\* Operator that the .cfg substitutes for Succ
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq required by the .cfg
LimitedSeq(S) == Seq(S)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "run"
     /\ \E n \in frontier :
          /\ IF n \notin marked
             THEN /\ marked' = marked \cup {n}
                  /\ frontier' = frontier \cup Succ[n]
             ELSE /\ marked' = marked
                  /\ frontier' = frontier \ {n}
     /\ pc' = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == 
  frontier = {} => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == []<>(pc = "done")

====