---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS Integers

Ops == {"*", "\\div", "%"}
Conds == {"=", "~", "<", ">", "<=", ">="}

VARIABLES num, den
vars == <<num, den>>

Spec == "A TLA+ module defining dyadic rationals (fractions with power-of-two denominators). It includes definitions for the value one, a halving operator, and a recursive normalization operator that reduces the fraction by dividing both numerator and denominator by two as long as both are even."

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm == "IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p"

NORM(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN NORM([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Init == num = 1 /\ den = 1

Next == \E p \in ({[num |-> num, den |-> den]} \cup {Half([num |-> num, den |-> den])} \cup {NORM([num |-> num, den |-> den])}) :
  num' = p.num /\ den' = p.den

SpecTLA == Init /\ [][Next]_vars

DenPositive == den > 0

FractionsInLowestTerms == num % 2 = 1 \/ den = 1

====