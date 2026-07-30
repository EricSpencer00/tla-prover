---- MODULE DyadicRationals ----
EXTENDS Integers

\* One and Half are two dyadic rational constants; Norm is a recursive
\* normalizer that removes common factors of two from a dyadic fraction.
CONSTANTS One, Half, Norm

VARIABLES r

vars == <<r>>

TypeOK ==
  /\ r \in [num : Nat, den : Nat]
  /\ One \in [num : Nat, den : Nat]
  /\ Half \in [num : Nat, den : Nat]
  /\ Norm \in [num : Nat, den : Nat] -> [num : Nat, den : Nat]

Init == r = One

\* Halve: split the denominator into two, leaving the value unchanged.
Halve == r' = [num |-> r.num, den |-> r.den * 2]

\* Normalize: recursively strip common factors of two from numerator and
\* denominator; the IF-THEN-ELSE structure must be preserved exactly.
Normalize ==
  r' = IF r.num % 2 = 0 /\ r.den % 2 = 0
          THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
          ELSE r

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

RationalInvariant == r.den > 0

NormalizationFixes == (r.den % 2 = 0) => (r.num % 2 = 1 \/ r.den % 2 = 1)

====