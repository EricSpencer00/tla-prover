---- MODULE DyadicRationals ----
EXTENDS Integers

\* Value one, as a dyadic rational with denominator one.
One == [num |-> 1, den |-> 1]

\* Halving operator that doubles the denominator.
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization: divide numerator and denominator by two as long
\* as both are even.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* The system's state is a single dyadic rational.
VARIABLES val

vars == <<val>>

\* Initially one.
Init == val = One

\* Halve, then normalize.
Next == val' = Norm(Half(val))

Spec == Init /\ [][Next]_vars

\* The denominator is always a power of two, so it is never odd unless one.
DenIsPowerOfTwo == val.den % 2 = 1 => val.den = 1

====