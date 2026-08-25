---- MODULE DyadicRationals ----
EXTENDS Integers

(* Dyadic rational record type *)
Dyadic == [num : Int, den : Nat]

(* The dyadic rational representing one *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Recursive normalization: remove common factor 2 from numerator and denominator *)
RECURSIVE Norm(_)

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====