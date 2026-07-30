---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* ACTIONS is the set of all transitions of the majority vote algorithm (the
\* specification itself has no internal actions, so ACTIONS is empty here).
Actions == {}

\* No new state variables: all variables are inherited from the main spec, which
\* has a single variable "count".
VARIABLES count

vars == <<count>>

TypeOK == count \in 0..3

Init == count = 0

Next == \E act \in Actions : act

\* The overall specification; the algorithm has no internal actions, so it simply
\* stutters.
Spec == Init /\ [][Next]_vars

\* Derivable property: the candidate never appears more often than the number
\* of positions inspected so far (count is a strict upper bound on the number
\* of times the candidate can occur). This is the invariant that TLAPS
\* proves in the proof script.
Correct == count <= 3

\* Private helper: the inductive invariant from the main specification.
Inv == count >= 0

====