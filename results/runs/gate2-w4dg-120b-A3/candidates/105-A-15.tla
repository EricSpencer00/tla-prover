---- MODULE DyadicRationals ----
EXTENDS Integers

\* This module captures dyadic rationals (fractions whose denominator is a power
\* of two) as pairs p.num/p.den. It provides a constant One, a halving operator
\* Half, and a recursive normalization operator Norm that repeatedly divides
\* both numerator and denominator by two whenever both are even.

CONSTANTS
  One
  Half
  Norm

VARIABLES p

vars == << p >>

TypeOK ==
  /\ p \in [num : Int, den : Int]
  /\ One = [num |-> 1, den |-> 1]
  /\ Half = [num |-> 0, den |-> 2]
  /\ Norm = [num |-> 1, den |-> 1]

Init ==
  /\ p = One
  /\ Norm = [num |-> 1, den |-> 1]

Next ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]
  /\ Norm' = [num |-> p.num \div 2, den |-> p.den \div 2]

Spec == Init /\ [][Next]_vars

DenominatorsPowerOfTwo == \E q \in Nat : p.den = 2 ^ q

NormalizeHalfDenominator ==
  (p.num % 2 = 0 /\ p.den % 2 = 0) => Norm = [num |-> p.num \div 2, den |-> p.den \div 2]

====