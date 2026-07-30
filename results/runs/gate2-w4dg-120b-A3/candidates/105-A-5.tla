---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ p \in [num : 0..3, den : 1..4]
  /\ One = [num |-> 1, den |-> 1]
  /\ Half = [num |-> 1, den |-> 2]

Init == p = One

Halve == p' = [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

Next == Halve

Spec == Init /\ [][Next]_vars

NormIsFixedPoint ==
  \A p \in [num : 0..3, den : 1..4] : Norm(p) = Norm(Norm(p))

AllDyadicFractionsReachable ==
  \A p \in [num : 0..3, den : 1..4] : (p \in {One, Half}) => (p \in {q \in [num : 0..3, den : 1..4] : (\E n \in Nat : p = [num |-> (1 \div 2^n), den |-> 2^n])})

====