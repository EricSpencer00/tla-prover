---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Backend pragma operators (place‑holders for the various provers)
\* ----------------------------------------------------------------------
Zenon(expr, timeout)   == TRUE
Isabelle(expr, timeout)== TRUE
CVC3(expr, timeout)    == TRUE
Yices(expr, timeout)   == TRUE
VeriT(expr, timeout)   == TRUE
Z3(expr, timeout)      == TRUE
SPASS(expr, timeout)   == TRUE
LS4(expr, timeout)     == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule operators (names reserved for future use)
\* ----------------------------------------------------------------------
InvarianceRule(P)      == []P
WellFormednessRule(P) == P
StrongFairnessRule(P) == WF_vars(P)
WeakFairnessRule(P)   == SF_vars(P)
StepSimulationRule(P, Q) == (P => Q)

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description
\* ----------------------------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S : ~ (UNIV \subseteq S)

\* ----------------------------------------------------------------------
\* Minimal specification skeleton (no state variables)
\* ----------------------------------------------------------------------
Init == TRUE
Next == TRUE
SPECIFICATION == Init /\ [] [Next]_<<>>
INVARIANTS == {}
PROPERTIES == {}

====