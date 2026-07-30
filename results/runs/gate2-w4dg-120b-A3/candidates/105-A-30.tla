---- MODULE DyadicRationals ----
EXTENDS Integers

\* DyadicRationals: a set of fractions with a power-of-two denominator, modeled as
\* records with integer numerator and denominator. The normalization operator
\* recursively divides both by two whenever they are both even.
\* Required identifiers: see the .cfg section of the prompt.

\* No explicit constants are required by the .cfg, so there are none. The module
\* still defines One, Half, and Norm as operators, exactly as the description
\* demands.

VARIABLES p

TypeOK == p \in [num : Int, den : Int]

Init == p = [num |-> 1, den |-> 1]

Next == \E p' \in [num : Int, den : Int] : p' = [num |-> p.num, den |-> p.den * 2]

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Spec == Init /\ [][Next]_p
====