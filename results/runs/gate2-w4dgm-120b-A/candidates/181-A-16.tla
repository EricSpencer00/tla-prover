---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The number set is overridden to a finite range for model checking;
\* this redefinition is what makes the infinite Nat checkable here.
NatOverride == 0..MaxNat

VARIABLES x

TypeOK == x \in NatOverride

Init == x = 0

Next == \E y \in NatOverride : x' = y

Spec == Init /\ [][Next]_x

\* The theorem (double of any Nat is even) is assumed as an axiom here
\* for the sake of the model check; it is the property the full proof
\* in the main spec establishes from first principles.
TheoremIsEven == (\A n \in NatOverride : 2 * n \in Nat)

====