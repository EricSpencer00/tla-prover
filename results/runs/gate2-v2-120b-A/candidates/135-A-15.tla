---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants required by the reference .cfg
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* Derived sets and functions (for readability)
\* ----------------------------------------------------------------------
Node == Nodes

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant (required)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Node
  /\ Frontier \subseteq Node
  /\ pc \in {"Init", "Step", "Done"}

\* ----------------------------------------------------------------------
\* Initial state (Spec.Init)
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Init"

\* ----------------------------------------------------------------------
\* Step action (Spec.Step)
\* ----------------------------------------------------------------------
Step ==
  /\ pc = "Init"
  /\ \E n \in Frontier :
       /\ Marked' = Marked \cup {n}
       /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked')
       /\ pc' = IF Frontier' = {} THEN "Done" ELSE "Init"
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation (Spec.Next) – includes stuttering in Done state
\* ----------------------------------------------------------------------
Next ==
  \/ Step
  \/ /\ pc = "Done"
     /\ UNCHANGED << Marked, Frontier, pc >>

\* ----------------------------------------------------------------------
\* Specification (Spec)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Inv1 ==
  /\ Marked \subseteq Node
  /\ Frontier \subseteq Node

Inv2 ==
  /\ \A n \in Marked : n = Root \/ \E m \in Marked : n \in Succ[m]

Inv3 ==
  Marked = Node

PartialCorrectness ==
  /\ pc = "Done"
  /\ Marked = Node

\* ----------------------------------------------------------------------
\* Liveness property (Termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM linking Spec to the named specification formula
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

=============================================================================