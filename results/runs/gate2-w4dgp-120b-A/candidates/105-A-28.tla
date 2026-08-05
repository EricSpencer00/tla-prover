---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

Init ==
  p = [num |-> 1, den |-> 1]

Next ==
  \/ p' = [num |-> p.num, den |-> p.den * 2]
  \/ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN p' = [num |-> p.num \div 2, den |-> p.den \div 2]
       ELSE p' = p

Spec == Init /\ [][Next]_vars

NatDenominator == p.den >= 1

RatioValueCorrect ==
  IF p.den = 0 THEN FALSE ELSE One = p.num / p.den
====