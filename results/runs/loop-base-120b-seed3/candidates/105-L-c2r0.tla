---- MODULE DyadicRationals ----
EXTENDS Integers

(*-------------------------------------------------------------------*)
(*  Dyadic rational numbers are represented as records with two     *)
(*  integer fields:                                                    *)
(*      num  – the numerator                                           *)
(*      den  – the denominator (always positive)                      *)
(*-------------------------------------------------------------------*)

Dyadic == [num : Int, den : Int]

(* One – the dyadic rational representing the integer 1 *)
One == [num |-> 1, den |-> 1]

(* Half – a function that halves a dyadic rational by doubling its
   denominator. *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* Norm – recursively normalises a dyadic rational by dividing both
   numerator and denominator by 2 while both are even. *)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

=============================================================================