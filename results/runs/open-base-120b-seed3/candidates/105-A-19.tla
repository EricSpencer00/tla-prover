---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rational numbers are represented as records with fields
  num (numerator) and den (denominator).  The denominator is always
  a power of two.  The module defines:
    - One   : the dyadic rational 1/1
    - Half  : a function that halves a dyadic rational
    - Norm  : a recursive normalization operator that removes common
             factors of 2 from numerator and denominator
  It also provides a trivial temporal specification with the
  required operators: SPECIFICATION, INIT, NEXT, INVARIANTS,
  PROPERTIES.
-----------------------------------------------------------------*)

VARIABLES dr

(* ----------------------------------------------------------------
   Record constructors (used in definitions below)
   ---------------------------------------------------------------- *)
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* ----------------------------------------------------------------
   Simple state machine to illustrate use of the operators.
   ---------------------------------------------------------------- *)
Init == dr = One

Next ==
  \/ dr' = Half(dr)
  \/ dr' = Norm(dr)

(* ----------------------------------------------------------------
   Required top‑level operators.
   ---------------------------------------------------------------- *)
INIT == Init
NEXT == Next
SPECIFICATION == Init /\ [][Next]_<<dr>>
INVARIANTS == TRUE
PROPERTIES == TRUE

====