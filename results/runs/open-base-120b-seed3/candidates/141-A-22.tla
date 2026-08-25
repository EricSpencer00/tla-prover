---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxLen == 5

LimitedSeq(s) == 
  /\ s \in Seq(Nodes)
  /\ Len(s) <= MaxLen

\* Successor set of a set of nodes
SuccSet(S) == UNION { Succ[n] : n \in S }

\* Reachability from a set of nodes (finite closure)
RECURSIVE Reach(_)
Reach(S) == 
  IF S = {} THEN {} 
  ELSE S \cup Reach(SuccSet(S))

\* ----------------------------------------------------------------------
\* Operator required by the .cfg substitution
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == { m \in Nodes : m # n }

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
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
ChooseNode == 
  /\ frontier # {}
  /\ \E n \in frontier:
       /\ IF n \\notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = pc
          ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = pc

Terminate == 
  /\ frontier = {}
  /\ pc = "Running"
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next == 
  \/ Terminate
  \/ ChooseNode

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

Inv1 == \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == 
  /\ pc = "Done"
  /\ marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====