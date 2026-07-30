---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

\* p is a dyadic rational in record form; Norm enforces the ratio to be reduced
\* by stripping common factors of two from numerator and denominator.
VARIABLES p

vars == << p >>

Record(n, d) == [num |-> n, den |-> d]

Init == p = Record(1, 1)

\* One: the dyadic rational 1 (1/1); Half: the dyadic rational 1/2.
TypeOK ==
  /\ One = Record(1, 1)
  /\ Half = Record(1, 2)
  /\ p \in (Nat \X Nat)

Spec == Init

Norm(p) ==
  IF (p.num % 2 = 0) /\ (p.den % 2 = 0)
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Halve == p' = Record(p.num, p.den * 2)

Next == Halve

Spec == Init /\ [][Next]_vars

\* Every reachable dyadic rational is already in lowest terms: numerator and
\* denominator never share a factor of 2.
Normalized == (p.num % 2 = 1) \/ (p.den % 2 = 1)

====