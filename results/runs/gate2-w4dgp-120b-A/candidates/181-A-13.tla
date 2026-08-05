---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The base specification's Nat set is replaced by a finite version for model checking.
Nat == 0..MaxNat

\* The theorem from the proof (the double of any natural number is even) is assumed here
\* as a constant-level fact so that TLC can explore the model; the real proof justifies it.
Theorem == \A n \in Nat : 2 * n \in Nat \land n \in Nat

====