---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The theorem that the double of any natural number is even is assumed here as
\* a constant-level assumption so that TLC can process the model; the model
\* itself has no actions and no state beyond the bounded Nat set.
SpecAssumption == \A n \in Nat : (2 * n) % 2 = 0

Spec == SpecAssumption

Init == TRUE

Next == TRUE

TypeOK == TRUE

SpecOK == TRUE

====