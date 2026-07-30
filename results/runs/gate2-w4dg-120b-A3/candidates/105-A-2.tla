---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

TypeOK == /\ p \in [num: 0..2, den: {1, 2}]
          /\ One \in [num: 0..2, den: {1, 2}]
          /\ Half \in [num: 0..2, den: {1, 2}]

Init == /\ p = [num |-> 1, den |-> 1]
        /\ One = [num |-> 1, den |-> 1]
        /\ Half = [num |-> 1, den |-> 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0
           THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
           ELSE q

Next == /\ p' = Norm([num |-> p.num, den |-> p.den * 2])
        /\ UNCHANGED <<One, Half>>

Specification == Init /\ [][Next]_vars

InvariantDenominatorPowerOfTwo ==
  \A k \in 1..2 : (p.den = 2 ^ k) => TRUE

PropertyHalvingIsReversible ==
  Norm([num |-> Half.num, den |-> Half.den * 2]) = Half

====