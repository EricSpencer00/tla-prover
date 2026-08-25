---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(*--- Override of the infinite natural numbers with a finite range ---*)
NatOverride == 0 .. MaxNat

VARIABLE n

(*--- Initial state: n is any natural number in the finite range ---*)
INIT == n \in NatOverride

(*--- No state changes; the property is checked on the initial state ---*)
NEXT == UNCHANGED n

(*--- Overall specification ---*)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(*--- Helper definition for evenness ---*)
Even(x) == x % 2 = 0

(*--- Invariant stating that double of n is even ---*)
INVARIANTS == Even(2 * n)

(*--- Property asserting the theorem for all numbers in the finite range ---*)
PROPERTIES == \A m \in NatOverride : Even(2 * m)
====