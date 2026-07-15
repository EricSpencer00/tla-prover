---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat

\* Ensure that MaxNat is a natural number within the allowable range.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

\* Preserve the original assumption without changing its semantics.
ASSUME T1
====