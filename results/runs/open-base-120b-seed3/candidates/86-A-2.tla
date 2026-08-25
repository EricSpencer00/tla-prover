---- MODULE TLAPS ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT AllVals

\* For the purpose of this module we assume AllVals is the set of natural
\* numbers (any non‑empty set would do).
ASSUME AllVals = Nat

\* ----------------------------------------------------------------------
\* Backend provers (place‑holders for TLAPS)
\* ----------------------------------------------------------------------
Zenon(p)    == TRUE
Isabelle(p) == TRUE
CVC3(p)     == TRUE
Yices(p)    == TRUE
VeriT(p)    == TRUE
Z3(p)       == TRUE
SPASS(p)    == TRUE
LS4(p)      == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names only; definitions are placeholders)
\* ----------------------------------------------------------------------
InvariantRule(P, Q) == TRUE
WellFormedRule(P)   == TRUE
StrongFairness(R)   == TRUE
WeakFairness(R)     == TRUE
StepSimulation(R, S) == TRUE

\* ----------------------------------------------------------------------
\* Fundamental theorems
\* ----------------------------------------------------------------------
SetExtensionality ==
  \A S, T \in SUBSET AllVals :
    (\A x \in AllVals : (x \in S) <=> (x \in T)) => S = T

NoSetContainsAll ==
  \A S \in SUBSET AllVals : ~(\A x \in AllVals : x \in S)

\* ----------------------------------------------------------------------
\* Trivial state for completeness (no real behavior)
\* ----------------------------------------------------------------------
VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\* Required identifiers (as requested)
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT           == Init
NEXT           == Next
INVARIANTS     == {SetExtensionality, NoSetContainsAll}
PROPERTIES     == {}

====