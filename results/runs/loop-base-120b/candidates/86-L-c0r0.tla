---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\*  Backend provers for TLAPS.  The definitions are placeholders; the
\*  proof manager interprets the operator names and arguments.
\* ----------------------------------------------------------------------
Zenon(expr, timeout) == TRUE
Isabelle(expr, timeout) == TRUE
CVC3(expr, timeout) == TRUE
Yices(expr, timeout) == TRUE
VeriT(expr, timeout) == TRUE
Z3(expr, timeout) == TRUE
SPASS(expr, timeout) == TRUE
LS4(expr, timeout) == TRUE

\* ----------------------------------------------------------------------
\*  Temporal‑logic proof rules (placeholders for the actual rules).
\* ----------------------------------------------------------------------
Init == TRUE
Next == TRUE

InvarianceRule(I) == 
  /\ \A s : Init => I(s)
  /\ \A s, s' : Next => (I(s) => I(s'))
  /\ I

WellFormednessRule(p) == TRUE
StrongFairnessRule(F) == TRUE
WeakFairnessRule(F) == TRUE
StepSimulationRule(R) == TRUE

\* ----------------------------------------------------------------------
\*  Fundamental theorems.
\* ----------------------------------------------------------------------
CONSTANT Universe

SetExtensionality == 
  \A A, B \in SUBSET Universe :
    (\A x \in Universe : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet == 
  \A S \in SUBSET Universe : \E x \in Universe : x \notin S

====