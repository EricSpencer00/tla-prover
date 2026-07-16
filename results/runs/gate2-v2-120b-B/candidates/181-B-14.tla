------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

\* Assume MaxNat is a natural number. This is needed for the NatOverride
\* definition to be a valid finite subset of Nat.
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

\* Preserve the original placeholder assumption T1.
ASSUME T1
====================================================================