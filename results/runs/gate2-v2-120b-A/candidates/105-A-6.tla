---- MODULE DyadicRationals ----
EXTENDS Integers

(*--------------------------------------------------------------------
  Dyadic rationals are fractions whose denominator is a power of two.
  Each rational is represented as a record with two fields:
     num : numerator   (integer)
     den : denominator (positive integer, power of two)
--------------------------------------------------------------------*)

VARIABLE p

(*--------------------------------------------------------------------
  Constants and operator definitions required by the description
--------------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

(* The normalization operator reduces the fraction by repeatedly
   dividing numerator and denominator by two while both are even. *)
Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

(*--------------------------------------------------------------------
  Initial state: the system starts with the dyadic rational 1.
--------------------------------------------------------------------*)
Init == p = One

(*--------------------------------------------------------------------
  Next-state relation:
  - Halve the current rational (multiply denominator by 2)
  - Or, if both numerator and denominator are even, apply one step
    of normalization (divide both by 2)
  After either operation we re‑normalize to keep the representation
  canonical.
--------------------------------------------------------------------*)
Halve == [num |-> p.num, den |-> p.den * 2]

NormalizeStep == [num |-> p.num \div 2, den |-> p.den \div 2]

Next ==
  \/ p' = Norm(Halve)
  \/ /\ p.num % 2 = 0 /\ p.den % 2 = 0
     /\ p' = Norm(NormalizeStep)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

=============================================================================