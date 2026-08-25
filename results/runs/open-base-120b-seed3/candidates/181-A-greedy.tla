---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n ranges over the finite natural numbers
INIT == n \in NatOverride

\* Next-state relation: n may take any value in the finite range
NEXT == /\ n' \in NatOverride

\* Specification of the system
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Definition of evenness using the finite NatOverride
Even(m) == \E k \in NatOverride : m = 2 * k

\* Invariant stating that double of any n is even
INVARIANTS == Even(2 * n)

\* Property (same as invariant) for TLC checking
PROPERTIES == Even(2 * n)

\* Constant‑level assumption that the theorem holds (used to enable TLC)
ASSUME Theorem == \A n \in NatOverride : Even(2 * n)

====