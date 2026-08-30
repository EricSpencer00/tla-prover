---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init == p = One

Halve == p' = Half

Recurse == p' = Norm(p)

Next == Halve \/ Recurse

Spec == Init /\ [][Next]_vars

NoZeroDenominator == p.den # 0

DenominatorPowerOfTwo == \A k \in Nat : 2^k = p.den

====