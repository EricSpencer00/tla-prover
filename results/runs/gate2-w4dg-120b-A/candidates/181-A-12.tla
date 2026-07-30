---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANTS MaxNat, Nat

\* The bounded model checking configuration for the proof that the double
\* of any natural number is even.  It inherits the mathematical definitions
\* from the base specification (the theorem itself lives there) and
\* replaces the unbounded Nat with the finite range zero..MaxNat so that TLC
\* can check the property.

VARIABLES x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == \E y \in Nat : x' = y

Spec == Spec == Init /\ [][Next]_vars

Theorem == \A n \in Nat : (n + n) % 2 = 0

====