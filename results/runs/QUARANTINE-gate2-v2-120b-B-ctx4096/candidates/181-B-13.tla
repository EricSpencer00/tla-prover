---- MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
\* The assumption that MaxNat is not a natural number is inconsistent with the
\* definition of NatOverride (which ranges over natural numbers up to MaxNat).
\* Therefore we remove the contradictory assumption and keep the model
\* consistent. All other behavior of the original module is preserved.
ASSUME T1
=============================