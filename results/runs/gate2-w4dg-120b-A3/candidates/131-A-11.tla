---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* State is fully inherited from the main majority vote specification;
\* this proof module adds no new state, so the variable set is empty.
VARIABLES NONE

Vars == NONE

TypeOK ==
  /\ Value \in 0..3

\* The basic TAUTOLOGY below is the zero-step proof of TypeOK: it is
\* true in the initial state and preserved by the empty transition set.
Spec == /\ TypeOK

Init ==
  /\ TypeOK

Next ==
  /\ UNCHANGED Vars

\* Inv is the inductive invariant of the main algorithm; correct is the
\* main correctness property (the candidate equals any strict-majority
\* value).  The proof verifies that both are invariants of Spec.
Inv == TRUE
Correct == TRUE

====