---- MODULE DyadicRationals ----
EXTENDS Integers

(* ------------------------------------------------------------------- *)
(*  Dyadic rational numbers are represented as records with fields      *)
(*  num : integer numerator                                           *)
(*  den : natural denominator (positive)                               *)
(* ------------------------------------------------------------------- *)

Dyadic == [num : Int, den : Nat]

(* The dyadic rational representing the value one *)
One == [num |-> 1, den |-> 1]

(* Halving operator: multiplies the denominator by 2 *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* ------------------------------------------------------------------- *)
(*  Normalization operator: repeatedly divide numerator and denominator*)
(*  by 2 while both are even.                                         *)
(* ------------------------------------------------------------------- *)

RECURSIVE Norm(_)

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====