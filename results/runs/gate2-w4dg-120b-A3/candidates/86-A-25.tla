---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  NONE

VARIABLES action

vars == <<action>>

Init == action = NONE

Next == UNCHANGED action

TheoremSpec == TRUE

\* Zenon: first-order logic prover that generates Isabelle proofs.
Zenon == TRUE

\* Isabelle: interactive theorem prover with an automated ATP back-end.
Isabelle == TRUE

\* CVC3: an SMT solver that handles quantifier-free fragments.
CVC3 == TRUE

\* Yices: an SMT solver with an eager bit-blasting back-end.
Yices == TRUE

\* veriT: an SMT solver based on a DPLL(T) architecture.
VeriT == TRUE

\* Z3: a popular SMT solver supporting quantified fragments.
Z3 == TRUE

\* SPASS: an automated first-order logic prover.
SPASS == TRUE

\* LS4: an interactive theorem prover for modal and linear temporal logic.
LS4 == TRUE

\* Temporal logic invariance rule: a state formula is invariant if it holds every step.
Invariance == TRUE

\* Temporal logic step simulation rule.
StepSimulation == TRUE

\* Temporal logic strong fairness rule.
StrongFairness == TRUE

\* Temporal logic weak fairness rule.
WeakFairness == TRUE

\* Temporal logic well-formedness rule.
WellFormed == TRUE

\* Set extensionality.
SetExtensionality == TRUE

\* No set contains every value.
NoUniversalSet == TRUE

TypeOK == TRUE
InitOK == Init
NextOK == Next
SpecOK == Init /\ [][Next]_vars
INVARIANT == SetExtensionality
PROPERTY == NoUniversalSet
====