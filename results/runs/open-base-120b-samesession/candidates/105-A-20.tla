---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rational numbers are represented as records with fields
  num (integer numerator) and den (natural denominator). The
  denominator is always positive.
-----------------------------------------------------------------*)
Dyadic == [num : Int, den : Nat]

(* The dyadic rational representing the number one *)
One == [num |-> 1, den |-> 1]

(* Halving operation: multiplies the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization: repeatedly divide numerator and denominator by 2
   while both are even. *)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN
    Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

====