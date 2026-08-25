---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rational numbers are represented as records with two integer
  fields:
     num  = numerator
     den  = denominator (always positive)
-----------------------------------------------------------------*)
Dyadic == [num : Int, den : Int]

(* The dyadic rational representing the integer 1. *)
One == [num |-> 1, den |-> 1]

(* Halving a dyadic rational: keep numerator, double denominator. *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Normalization: repeatedly divide numerator and denominator by 2
   while both are even. *)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====