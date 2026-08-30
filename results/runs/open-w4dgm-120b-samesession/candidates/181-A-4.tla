---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* This module redefines Nat as a finite version of the infinite constant from
\* Naturals, keeping the same name so the substitution in the .cfg is legal.
Nat == 0..MaxNat

\* The model-checking configuration that assumes the theorem as a constant-level
\* assumption and bounds the natural numbers.
SpecAssumption == TRUE

====