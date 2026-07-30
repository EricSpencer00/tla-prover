---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
  /\ p \in [num : 0..3, den : {1, 2}]

SpecD ==
  /\ p.num \in 0..3
  /\ p.den \in {1, 2}

Init ==
  /\ p = One

Next ==
  \/ p' = Half
  \/ p' = Norm(p)
  \/ p' = [num |-> p.num, den |-> p.den * 2]
  \/ p' = [num |-> p.num \div 2, den |-> p.den \div 2]

Spec == SpecD /\ Init /\ Next

HalfSpec ==
  /\ p' = Half
  /\ UNCHANGED p

NormSpec ==
  /\ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
          THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
          ELSE p
  /\ UNCHANGED p

NormIsIdempotent ==
  Norm(Norm(p)) = Norm(p)

====