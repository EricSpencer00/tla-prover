---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* No state variables are required by the description, but a dummy
\* variable is introduced so that a well‑formed temporal specification can
\* be written.
\* ----------------------------------------------------------------------
VARIABLE dummy

\* ----------------------------------------------------------------------
\* Init and Next actions (trivial because the system has no substantive
\* state).  The dummy variable ranges over Nat and never changes.
\* ----------------------------------------------------------------------
Init == dummy \in Nat
Next == dummy' = dummy

\* ----------------------------------------------------------------------
\* Specification, invariants and properties required by the task.
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_dummy
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Foundational theorems required by the description.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) \Leftrightarrow (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  ~\E S : S = UNIV

====