---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Evenness predicate
IsEven(x) == x % 2 = 0

\* Initial state: choose any n within the finite range
INIT == n \in NatOverride

\* No state changes; the property is checked on the initial state
NEXT == UNCHANGED n

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Invariant to be checked by TLC
INVARIANTS == IsEven(2 * n)

\* Property (theorem) to be checked by TLC
PROPERTIES == IsEven(2 * n)

====