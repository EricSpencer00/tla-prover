---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat

\* Ensure that MaxNat is a natural number.
ASSUME MaxNat \in Nat

\* Define NatOverride to be the range of natural numbers up to MaxNat.
NatOverride == 0 .. MaxNat

\* Instantiate the behavior of the extended module with the overridden NAT set.
T1 == INSTANCE sums_even WITH Nat <- NatOverride

====