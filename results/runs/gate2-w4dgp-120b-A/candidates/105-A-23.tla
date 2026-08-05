---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
CONSTANTS Half
CONSTANTS Norm

VARIABLES p
vars == <<p>>

TypeOK ==
  /\ p.num \in Integers
  /\ p.den \in Integers

Init ==
  /\ p = One

Next ==
  \/ p' = Half
  \/ p' = Norm
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

OneDef ==
  One = [num |-> 1, den |-> 1]

HalfDef ==
  Half = [num |-> p.num, den |-> p.den * 2]

NormDef ==
  Norm = IF p.num % 2 = 0 /\ p.den % 2 = 0
           THEN [num |-> p.num \div 2, den |-> p.den \div 2]
           ELSE p

====