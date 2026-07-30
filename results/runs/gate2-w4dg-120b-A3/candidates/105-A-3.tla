---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers

\* A dyadic rational is a fraction with a denominator that's a power of two.
\* ONE is the fraction 1/1. Halve(p) inserts a power of two in the denominator
\* and Normalise(p) recursively divides numerator and denominator by two
\* whenever both are even, so 2/2 normalises to 1/1, 2/4 to 1/2, etc.

CONSTANTS Integers

RECURSIVE Norm(_)
Norm(p) ==
  IF (p.num % 2 = 0) /\ (p.den % 2 = 0)
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

One == [num |-> 1, den |-> 1]
Half(p) == [num |-> p.num, den |-> p.den * 2]

VARIABLES rat
vars == <<rat>>

Init == rat = One
Next == rat' = Half(Norm(rat))
Spec == Init /\ [][Next]_vars
Rational == rat.num % 2 = 1 \/ rat.den % 2 = 1

TypeOK ==
  /\ rat.num \in Naturals
  /\ rat.den \in Naturals
  /\ rat.den # 0
====