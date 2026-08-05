---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS p

ASSUME p \in [num : Nat, den : Nat]

Vars == [num : Nat, den : Nat]

One == [num |-> 1, den |-> 1]

Half == [num |-> Vars.num, den |-> Vars.den * 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE
        p

Init ==
    /\ Vars.num = 1
    /\ Vars.den = 1

Next ==
    /\ Vars' = Half
    /\ UNCHANGED p

Spec ==
    /\ Init
    /\ [][Next]_Vars

TypeOK ==
    /\ Vars.num \in Nat
    /\ Vars.den \in Nat

Normed ==
    Vars = Norm(Vars)

====