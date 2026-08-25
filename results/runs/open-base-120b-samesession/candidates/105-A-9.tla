---- MODULE DyadicRationals ----
EXTENDS Integers

(*--------------------------------------------------------------------
  Dyadic rationals are represented as records with integer numerator
  and natural denominator.  The denominator is intended to be a
  power of two, but this module does not enforce that invariant.
--------------------------------------------------------------------*)

Dyadic == [num : Int, den : Nat]

(* The dyadic rational representing the number one *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by two *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Recursive normalization: repeatedly divide numerator and
   denominator by two while both are even. *)
RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====