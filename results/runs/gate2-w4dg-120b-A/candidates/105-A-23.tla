---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES rat

vars == <<rat>>

TypeOK == rat \in [num : Int, den : Int]

Init == rat = One

Next == rat' = Half \/ rat' = Norm

Spec == Init /\ [][Next]_rat

RatIsNormal == IF rat.num % 2 = 0 /\ rat.den % 2 = 0 THEN Norm = rat ELSE TRUE

====