---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

(* --- Constants representing specific dyadic rationals --- *)
One  == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

(* --- Normalization operator: removes common factor 2 from numerator and denominator --- *)
RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* --- Initialization and next-state relation (trivial for illustration) --- *)
Init == p = One

Next == UNCHANGED p

(* --- Standard specification helpers --- *)
SPECIFICATION == Init /\ [] [Next]_<<p>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====