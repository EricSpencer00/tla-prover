---- MODULE DyadicRationals ----
EXTENDS Integers

(* Value representing the dyadic rational 1/1 *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization operator: repeatedly divide numerator and denominator by 2 
   while both are even *)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

====