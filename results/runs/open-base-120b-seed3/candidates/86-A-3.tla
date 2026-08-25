---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend provers (pragmas) – defined as simple stubs.
\* ----------------------------------------------------------------------
Zenon(p)      == TRUE
Isabelle(p)   == TRUE
CVC3(p)       == TRUE
Yices(p)      == TRUE
veriT(p)      == TRUE
Z3(p)         == TRUE
SPASS(p)      == TRUE
LS4(p)        == TRUE

\* ----------------------------------------------------------------------
\* Temporal logic proof rules (place‑holders).
\* ----------------------------------------------------------------------
Invariance(P)          == TRUE
WellFormedness(P)     == TRUE
StrongFairness(F)     == TRUE
WeakFairness(F)       == TRUE
StepSimulation(Sim)   == TRUE

\* ----------------------------------------------------------------------
\* Specification skeleton (no state variables).
\* ----------------------------------------------------------------------
Init == TRUE

Next == UNCHANGED <<>>   \* No variables to change.

SPECIFICATION == Init /\ [][Next]_<<>>

INVARIANTS == {}

PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Foundational theorems.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  ASSUME S \in SUBSET UNIV,
         T \in SUBSET UNIV,
         \A x \in UNIV : (x \in S) \equiv (x \in T)
  PROVE  S = T

THEOREM NoSetContainsAll ==
  ASSUME S \in SUBSET UNIV
  PROVE  \E x \in UNIV : x \notin S

====