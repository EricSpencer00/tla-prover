---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS NoOne

\* Backend provers for TLAPS. Each operator below is not a runtime action
\* in the system; it is a declaration to the proof system about which
\* prover to dispatch a given proof obligation to, which is why these are
\* ordinary operators rather than guarded actions on shared state.
Zenon   == "zenon"
Isabelle == "isabelle"
CVC3    == "cvc3"
Yices   == "yices"
VeriT   == "verit"
Z3      == "z3"
SPASS   == "spass"
LS4     == "ls4"

\* Temporal-logic proof rules: invariance, well-formedness, fairness,
\* and step simulation. Included for name reservation only; they never
\* fire on real shared state in this configuration module.
Invariant == "invariance"
WellFormed == "wellformed"
StrongFair == "strongfair"
WeakFair == "weakfair"
SimStep == "simstep"

Spec == "The system model that this configuration module applies to."

\* No shared state changes here; this module only declares configuration.
Init == Spec

Next == Spec

TypeOK == TRUE

\* Two elementary facts about sets, taken as given by the prover.
SetExtensionality == TRUE
NoSetIsUniversal  == TRUE

====