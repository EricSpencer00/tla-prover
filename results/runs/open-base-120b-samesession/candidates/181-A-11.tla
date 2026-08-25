---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial predicate
INIT == n \in NatOverride

\* Stuttering step (no state change)
NEXT == UNCHANGED n

\* Complete specification
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Evenness predicate using the (infinite) Nat set
IsEven(m) == \E k \in Nat : m = 2 * k

\* Invariant: the double of the current n is even
INVARIANTS == IsEven(2 * n)

\* Property to be checked over the entire finite range
PROPERTIES == \A m \in NatOverride : IsEven(2 * m)
====