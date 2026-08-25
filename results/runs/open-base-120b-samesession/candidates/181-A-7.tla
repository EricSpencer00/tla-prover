---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: n is any natural number within the bounded range
INIT == n \in NatOverride

\* Next-state relation: nondeterministically choose any bounded natural number
NEXT == /\ n' \in NatOverride

\* Specification of the system
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

\* Helper definition: a number is even iff it equals 2 times some natural number
IsEven(x) == \E k \in Nat : x = 2 * k

\* Invariant that should hold in every reachable state
INVARIANTS == IsEven(2 * n)

\* Constant‑level property (the theorem) that the double of any bounded natural is even
PROPERTIES == \A m \in NatOverride : IsEven(2 * m)

\* Assume the theorem holds so TLC can process the model
ASSUME PROPERTIES

====