---- MODULE DyadicRationals ----
EXTENDS Integers

\* Dyadic rationals: numerator and denominator, with a recursive normalizer
\* that divides both by two while both are even.
VARIABLES p

vars == <<p>>

TypeOK ==
  /\ p.num \in Integer
  /\ p.den \in Integer

Init ==
  /\ p.num = 1
  /\ p.den = 1

\* Halve the rational by doubling the denominator.
Half == [num |-> p.num, den |-> p.den * 2]

\* Recursively divide numerator and denominator by two while both are even,
\* then return the result (a canonical choice that makes the repeat loop
\* finite).
Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
  THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
  ELSE q

One == [num |-> 1, den |-> 1]

Next ==
  \/ p' = Half
  \/ p' = Norm(p)

Spec == Init /\ [][Next]_vars

\* The invariant: the denominator is never zero, so division by zero is
\* avoided entirely; also the fraction stays positive.
DenPos == p.den > 0

Bounded == p.num <= 16

====