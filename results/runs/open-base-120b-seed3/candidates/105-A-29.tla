---- MODULE DyadicRationals ----
EXTENDS Integers

(* ---------------------------------------------------------------------- *)
(*  Dyadic rational numbers are represented as records with two fields:   *)
(*    num : the integer numerator                                        *)
(*    den : a positive integer denominator that is a power of two       *)
(* ---------------------------------------------------------------------- *)

IsPowerOfTwo(d) == 
  \E k \in Nat : d = 2 ^ k

Dyadic == 
  { p \in [num : Int, den : Nat] : p.den > 0 /\ IsPowerOfTwo(p.den) }

(* ---------------------------------------------------------------------- *)
(*  The constant representing the dyadic rational 1/1                        *)
(* ---------------------------------------------------------------------- *)
One == [num |-> 1, den |-> 1]

(* ---------------------------------------------------------------------- *)
(*  Halving operator: multiplies the denominator by 2, leaving the numerator unchanged *)
(* ---------------------------------------------------------------------- *)
Half(p) == [num |-> p.num, den |-> p.den * 2]

(* ---------------------------------------------------------------------- *)
(*  Normalization operator: repeatedly divides numerator and denominator by 2 *)
(*  while both are even, yielding a dyadic rational in lowest terms.        *)
(* ---------------------------------------------------------------------- *)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* ---------------------------------------------------------------------- *)
(*  Optional sanity check: Normalization preserves the Dyadic set.          *)
(* ---------------------------------------------------------------------- *)
THEOREM NormPreservesDyadic == 
  \A p \in Dyadic : Norm(p) \in Dyadic

====