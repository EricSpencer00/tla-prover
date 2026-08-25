---- MODULE DyadicRationals ----
EXTENDS Integers

(* A dyadic rational is a record with integer numerator and positive natural denominator *)
Dyadic == { p \in [num : Int, den : Nat] : p.den > 0 }

(* The dyadic rational representing the value one *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by 2, leaving the numerator unchanged *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization operator: repeatedly divides numerator and denominator by 2 
   while both are even, yielding a reduced dyadic rational *)
RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====