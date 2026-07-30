---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES val

vars == <<val>>

TypeOK ==
  /\ One \in [num : 1, den : 1]
  /\ Half \in [num : 1, den : 2]
  /\ Norm \in [num : 1 .. 2, den : 1 .. 2]

Init ==
  /\ val = One

\* Halve the fraction: double the denominator, keeping the value unchanged.
Halve ==
  /\ val' = [num |-> val.num, den |-> val.den * 2]

\* Normalization is recursive: as long as both numerator and denominator are
\* even, divide them by 2. Tail call to remove the recursion from TLC's view.
Normalize ==
  /\ IF val.num % 2 = 0 /\ val.den % 2 = 0
       THEN val' = Norm([num |-> val.num \div 2, den |-> val.den \div 2])
       ELSE val' = val

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

Iv2 == TRUE

Prop2 == TRUE

====