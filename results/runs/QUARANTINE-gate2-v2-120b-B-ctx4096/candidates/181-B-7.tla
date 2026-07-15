---- MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
\* The original specification incorrectly assumed MaxNat ∉ Nat,
\* which caused the model checker to abort because it contradicts
\* the intended interpretation of MaxNat as a natural number bound.
\* We replace the contradictory assumption with a consistent one
\* that states MaxNat belongs to Nat and is strictly greater than 0.
ASSUME MaxNat \in Nat \ {0}
NatOverride == 0 .. MaxNat
ASSUME T1
====