---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers up to MaxNat
NatOverride == 0 .. MaxNat

VARIABLE n

\* Initial state: choose any n in the finite natural range
Init == n \in NatOverride

\* No state changes (stuttering)
Next == UNCHANGED n

\* Predicate that a value is even (exists a k such that x = 2*k)
IsEven(x) == \E k \in Nat : x = 2 * k

\* Invariant stating that the double of n is even
EvenDouble == IsEven(2 * n)

\* Full specification
SPECIFICATION == Init /\ [][Next]_<<n>>

\* Invariants for TLC to check
INVARIANTS == { EvenDouble }

\* Temporal properties for TLC to check
PROPERTIES == { []EvenDouble }

====