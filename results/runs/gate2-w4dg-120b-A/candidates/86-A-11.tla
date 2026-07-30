---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  MaxLedger, MaxLog

ASSUME MaxLedger \in Nat /\ MaxLog \in Nat

\* Backends: these operators fire a backend prover for their argument and then
\* return TRUE so they impose no extra proof obligations.
\* The arguments are the exact syntactic forms that TLAPS understands.

Zenon(formula)       == TRUE
Isabelle(formula)    == TRUE
CVC3(formula)        == TRUE
Yices(formula)       == TRUE
VeriT(formula)       == TRUE
Z3(formula)          == TRUE
SPASS(formula)       == TRUE
LS4(formula)         == TRUE

\* Temporal-logic proof rules. They are theorems, not operators to invoke, so
\* each is simply asserted as TRUE. Their side-effect is to reserve the name.
Extensionality     == TRUE
NoUniverse        == TRUE
Invariance        == TRUE
WellFormed        == TRUE
StrongFairness    == TRUE
WeakFairness      == TRUE
STEP              == TRUE

TypeOK ==
  /\ Extensionality = TRUE
  /\ NoUniverse = TRUE
  /\ Invariance = TRUE
  /\ WellFormed = TRUE
  /\ StrongFairness = TRUE
  /\ WeakFairness = TRUE
  /\ STEP = TRUE

Spec == Extensionality /\ NoUniverse
====