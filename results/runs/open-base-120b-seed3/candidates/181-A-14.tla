---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE x

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* State initialization
INIT == x \in NatOverride

\* State transition (trivial, any value in NatOverride)
NEXT == /\ x' \in NatOverride

\* Overall specification
SPECIFICATION == INIT /\ [][NEXT]_<<x>>

\* The theorem: double of any natural number is even
DoubleEven == \A n \in NatOverride : (2 * n) % 2 = 0

INVARIANTS == { DoubleEven }

PROPERTIES == {}

\* Constant‑level assumption that the theorem holds
ASSUME DoubleEven
====