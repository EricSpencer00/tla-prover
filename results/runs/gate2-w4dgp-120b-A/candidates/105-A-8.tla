---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p
vars == <<p>>

TypeOK == /\ p \in [num : Nat, den : Nat]
          /\ p.den \in {1, 2}

Init == /\ p = [num |-> 1, den |-> 1]
        /\ One = [num |-> 1, den |-> 1]
        /\ Half = [num |-> 1, den |-> 2]
        /\ Norm(p) = IF p.num % 2 = 0 /\ p.den % 2 = 0
                     THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
                     ELSE p

Next == /\ p' = Half
        /\ UNCHANGED <<One, Half, Norm>>

Spec == Init /\ [][Next]_vars
====