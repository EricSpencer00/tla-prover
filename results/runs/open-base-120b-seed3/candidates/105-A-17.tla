---- MODULE DyadicRationals ----
EXTENDS Integers

(*-------------------------------------------------------------------*)
(*  Dyadic rational numbers are represented as records with fields   *)
(*  num (integer numerator) and den (positive integer denominator). *)
(*-------------------------------------------------------------------*)

One == [num |-> 1, den |-> 1]

Half(p) == 
    /\ p \in [num : Int, den : Nat]
    /\ Norm([num |-> p.num, den |-> p.den * 2])

Norm(p) == 
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p
====