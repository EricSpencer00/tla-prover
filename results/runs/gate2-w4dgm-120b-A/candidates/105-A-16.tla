---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES val

vars == <<val>>

Init == val = One

Halt == \E p \in {val} : p.num % 2 = 0 /\ p.den % 2 = 0 /\ val' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
Next == Halt \/ (val' = val /\ TRUE)

Spec == Init /\ [][Next]_vars

TypeOK == val \in {One, Half} \/ (val.num \in Nat /\ val.den \in Nat)

DenNonZero == val.den # 0

ValueInDyadicRange ==
  /\ val.num \in 0..8
  /\ val.den \in {1, 2, 4, 8}
  /\ (val.num % 2 = 1 => val.den = 1)

====