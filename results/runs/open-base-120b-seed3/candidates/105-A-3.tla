---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rationals are represented as records with an integer numerator
  and a positive denominator that is a power of two.
-----------------------------------------------------------------*)
Dyadic ==
    { r \in [num : Int, den : Nat] :
        /\ r.den # 0
        /\ (\E k \in Nat : r.den = 2 ^ k) }

(*-----------------------------------------------------------------
  Constants and operators required by the description
-----------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]

Half(p) ==
    [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  Variables and the required top‑level operators
-----------------------------------------------------------------*)
VARIABLE p

INIT == p = One

NEXT == /\ p' \in Dyadic

SPECIFICATION == INIT /\ [][NEXT]_<<p>>

TypeInv == p \in Dyadic

INVARIANTS == { TypeInv }

PROPERTIES == { SPECIFICATION }

====