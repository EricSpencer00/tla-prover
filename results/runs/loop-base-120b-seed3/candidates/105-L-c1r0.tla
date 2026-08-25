---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rational numbers are represented as records with fields
  num (integer numerator) and den (positive integer denominator
  that is a power of two).  The module defines the constant One,
  the halving operator Half, and a recursive normalization operator
  Norm that divides numerator and denominator by two while both are
  even.
-----------------------------------------------------------------*)

CONSTANTS
  (* No external constants are required for this specification. *)

(*--- Types ------------------------------------------------------*)
Dyadic == { p \in [num : Int, den : Nat] :
               p.den # 0 /\ (\E k \in Nat : p.den = 2^k) }

(*--- Basic values -----------------------------------------------*)
One == [num |-> 1, den |-> 1]

(*--- Operators --------------------------------------------------*)
Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*--- Variables --------------------------------------------------*)
VARIABLE p

(*--- State predicates --------------------------------------------*)
Init == p = One

Next ==
  \/ p' = Half(p)
  \/ p' = Norm(p)

Spec == Init /\ [][Next]_<<p>>

(*--- Required identifiers for the configuration -----------------*)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == TRUE

====