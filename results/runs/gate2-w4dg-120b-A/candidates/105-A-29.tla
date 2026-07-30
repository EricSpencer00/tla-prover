---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ One \in {1}
  /\ Half \in {1}
  /\ Norm \in [num : Nat, den : Nat]

Init ==
  p = [num |-> 1, den |-> 1]

Next ==
  \/ p' = [num |-> p.num, den |-> p.den * 2]
  \/ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN p' = [num |-> p.num \div 2, den |-> p.den \div 2]
       ELSE p' = p

Spec == Init /\ [][Next]_vars

NarrowInvariant == p.den <= 8

DenomIsPowerOfTwo == \E e \in Nat : p.den = 2 ^ e

====