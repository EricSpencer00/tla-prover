---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each operator below is a TLAPS pragma that names a
\* prover and its timeout/tactic. The operators are deliberately side-effect
\* free (they return TRUE) because the proof system, not the spec, is what
\* actually dispatches the obligations.

ZenonProve == TRUE
IsabelleProve == TRUE
CVC3Prove == TRUE
YicesProve == TRUE
VeriTProve == TRUE
Z3Prove == TRUE
SPASSProve == TRUE
LS4Prove == TRUE

\* Temporal logic proof rules (reserved names from Lamport's TLA+ paper):
\* invariance, well-formedness, strong fairness, weak fairness, and step
\* simulation. They are theorems of the logic, not steps of the system.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

\* Foundational set-theoretic theorems that must always hold.
SetExtensionality == TRUE
NoUniversalSet == TRUE

\* The module's declared specification: the set of all operators it defines.
SPECIFICATION == { ZenonProve, IsabelleProve, CVC3Prove, YicesProve,
                    VeriTProve, Z3Prove, SPASSProve, LS4Prove,
                    InvarianceRule, WellFormednessRule, StrongFairnessRule,
                    WeakFairnessRule, StepSimulationRule,
                    SetExtensionality, NoUniversalSet }

\* The module has no state and no actions, so its initial state and its
\* next-state relation are the empty relation on the empty state.
Init == TRUE
Next == TRUE

\* The invariant set is the full SPECIFICATION, so every operator is
\* preserved by the (trivial) transition relation.
INVARIANTS == SPECIFICATION

\* The liveness set is empty: there is nothing to eventually happen.
PROPERTIES == {}

====