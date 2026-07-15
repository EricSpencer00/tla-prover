------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

\* Ensure MaxNat is a natural number within the usual bound.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

\* Preserve the original assumption T1 from the extended module.
ASSUME T1
====================================================================