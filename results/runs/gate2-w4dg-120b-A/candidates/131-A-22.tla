---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The module has no new state of its own; everything is inherited from the
\* majority-algorithm spec that it refines.  That spec is assumed to provide
\* the following symbols: Spec, TypeOK, Correct, Inv, Init, Next, and the
\* sequence v of input values.
\* The proof obligations below are what TLAPS checks, and they never introduce
\* fresh state — only new derived statements about the inherited one.

ASSUME Init \in [v : Nat -> Value]
ASSUME Spec \in BOOLEAN
ASSUME TypeOK \in BOOLEAN
ASSUME Correct \in BOOLEAN
ASSUME Inv \in BOOLEAN
ASSUME Next \in BOOLEAN

Spec == Spec

TypeOK == TypeOK

Correct == Correct

Inv == Inv

====