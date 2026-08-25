---- MODULE DyadicRationals ----
EXTENDS Integers

(* The dyadic rational representing the number one *)
One == [num |-> 1, den |-> 1]

(* Halving a dyadic rational: multiply the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization: repeatedly divide numerator and denominator by 2
   while both are even, producing a reduced dyadic rational. *)
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

====