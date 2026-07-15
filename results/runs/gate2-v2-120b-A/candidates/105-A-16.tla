---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
    One   \* dyadic rational representing the integer 1
  , Half  \* dyadic rational representing 1/2

(*-----------------------------------------------------------------
  Record type for dyadic rationals.
  The numerator may be any integer, the denominator must be a
  positive power of two (including 1).  The model does not enforce
  the power‑of‑two constraint directly; it is guaranteed by the
  way the operators are used.
-----------------------------------------------------------------*)
Dyadic == [num : Int, den : Nat]

(*-----------------------------------------------------------------
  Normalization operator: repeatedly divide numerator and denominator
  by two while both are even.  The recursion terminates because each
  division reduces the absolute value of the denominator.
-----------------------------------------------------------------*)
RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN Norm([num |-> p.num \div 2,
                  den |-> p.den \div 2])
       ELSE p

(*-----------------------------------------------------------------
  Explicit definitions required by the description.
-----------------------------------------------------------------*)
One == Norm([num |-> 1, den |-> 1])
Half == Norm([num |-> 1, den |-> 2])

(*-----------------------------------------------------------------
  State variable representing the current dyadic rational.
-----------------------------------------------------------------*)
VARIABLE p

(*-----------------------------------------------------------------
  Initial state: the rational value is One.
-----------------------------------------------------------------*)
Init == p = One

(*-----------------------------------------------------------------
  Halving step: replace p by its half and then normalize.
-----------------------------------------------------------------*)
Halve == p' = Norm([num |-> p.num,
                    den |-> p.den * 2])

(*-----------------------------------------------------------------
  Normalization step: apply Norm directly (no change if already
  normalized, otherwise reduces the fraction).
-----------------------------------------------------------------*)
Normalize == p' = Norm(p)

(*-----------------------------------------------------------------
  Next-state relation: either halve the current value or normalize it.
-----------------------------------------------------------------*)
Next == Halve \/ Normalize

(*-----------------------------------------------------------------
  Specification: the usual temporal formula.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

=============================================================================