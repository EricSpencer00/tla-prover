---- MODULE DyadicRationals ----
EXTENDS Integers
CONSTANTS One, Half, Norm
VARIABLES rec

TypeOK == rec \in [num : Nat, den : Nat]

Init == rec = One

Halve == rec' = Half

Normalize == rec' = IF rec.num % 2 = 0 /\ rec.den % 2 = 0
                 THEN Norm([num |-> rec.num \div 2, den |-> rec.den \div 2])
                 ELSE rec

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_rec

DenPositive == rec.den > 0

HalvingConverges == (\A k \in Nat : rec' = Norm([num |-> rec.num, den |-> rec.den * 2 ^ k]))
====