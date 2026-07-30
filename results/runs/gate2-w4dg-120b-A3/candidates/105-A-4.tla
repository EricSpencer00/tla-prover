---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ One \in [num : Int, den : Int]
  /\ Half \in [num : Int, den : Int]
  /\ Norm \in [num : (Int \cup {0}), den : (Int \cup {0})]
  /\ p \in [num : Int, den : Int]

Init ==
  /\ One = [num |-> 1, den |-> 1]
  /\ Half = [num |-> One.num, den |-> One.den * 2]
  /\ Norm = [num |-> 0, den |-> 0]
  /\ p = One

Next ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]
  /\ UNCHANGED <<One, Half, Norm>>

Spec == Init /\ [][Next]_vars

HalfIsDyadic ==
  /\ Half.num = 1
  /\ Half.den = 2

Normalization ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm = [num |-> p.num \div 2, den |-> p.den \div 2]
    ELSE Norm = p

====