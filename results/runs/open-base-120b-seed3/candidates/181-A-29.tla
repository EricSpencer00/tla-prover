---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANTS MaxNat

VARIABLE n

\* A finite version of Nat for model checking
NatOverride == { i \in Nat : i <= MaxNat }

\* Evenness predicate
IsEven(m) == m % 2 = 0

\* Initial state: n ranges over the finite naturals
Init == n \in NatOverride

\* Next state: nondeterministically choose any finite natural
Next == n' \in NatOverride

\* Full specification
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Invariants (none needed beyond the theorem)
INVARIANTS == TRUE

\* Property asserting that the double of any natural is even
PROPERTIES == \A m \in NatOverride : IsEven(2 * m)

====