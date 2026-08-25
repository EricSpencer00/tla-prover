---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

VARIABLES n

INIT == n \in NatOverride

NEXT == n' \in NatOverride

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* The theorem we want to check: double of any natural number is even
TheoremEven == \A m \in NatOverride : (2 * m) % 2 = 0

INVARIANTS == TheoremEven

PROPERTIES == TheoremEven

\* Assume the theorem holds at the constant level for TLC
ASSUME TheoremEven

====