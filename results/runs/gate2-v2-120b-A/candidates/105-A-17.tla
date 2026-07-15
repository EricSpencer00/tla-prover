---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers, TLC

\* ----------------------------------------------------------------------
\* Identifiers required by the description
\* ----------------------------------------------------------------------
ONE == 1

Half == [num |-> 1, den |-> 2]

\* Recursive normalization of dyadic rationals.
\* If both numerator and denominator are even, divide both by 2 and recurse.
\* Otherwise, return the fraction unchanged.
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

\* ----------------------------------------------------------------------
\* State variable and its type invariant
\* ----------------------------------------------------------------------
VARIABLES rat

\* The denominator is always a positive power of two.
DenIsPowerOfTwo(d) ==
    d > 0 /\ \A n \in Nat : d = 2^n

TypeOK ==
    /\ rat.num \in Nat
    /\ rat.den \in Nat
    /\ DenIsPowerOfTwo(rat.den)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    rat = [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Helper actions
\* ----------------------------------------------------------------------
HalfAction ==
    /\ rat.num' = rat.num
    /\ rat.den' = rat.den * 2
    /\ TypeOK'

NormAction ==
    /\ rat' = Norm(rat)
    /\ TypeOK'

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ HalfAction
    \/ NormAction

\* ----------------------------------------------------------------------
\* Specification and properties (place‑holders)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<rat>>

Inv == TypeOK

Prop == TRUE

====