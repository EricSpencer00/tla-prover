---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES rat

vars == <<rat>>

Rat == [num : Integers, den : Integers]

RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

TypeOK == rat \in Rat

Init == rat = One

Halve == rat' = Half

Map == rat' = [num |-> rat.num, den |-> rat.den * 2]

Next == Halve \/ Map

Spec == Init /\ [][Next]_vars

NormRecurses == Norm(rat) = rat

RatTerminated == (rat.den = 1) ~> (rat.den > 1)

====