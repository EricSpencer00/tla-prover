---- MODULE DyadicRationals ----
EXTENDS Integers

(* --constants and basic definitions-- *)
VARIABLES p

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

(*-- normalization operator (recursive) --*)
Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

(*-- initial state --*)
Init ==
  p = One

(*-- next-state relation (doubling denominator) --*)
Next ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]
  \/ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  \/ UNCHANGED p

(*-- specification as a temporal formula --*)
Spec ==
  /\ Init
  /\ [][Next]_<<p>>

(*-- invariant: denominator is always a power of two and numerator is integer --*)
DenPowerOfTwo(d) ==
  d = 1 \/ (\E k \in Nat : d = 2 ^ k)

Invariant ==
  /\ p.den > 0
  /\ DenPowerOfTwo(p.den)
  /\ p.num \in Int

(*-- optional property: the value represented by p stays within the dyadic rationals --*)
DyadicValue ==
  p.num % p.den = 0  \* placeholder, will be overridden by the theorem below

THEOREM Spec => []Invariant

====