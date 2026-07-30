---- MODULE DyadicRationals ----
EXTENDS Integers

\* Dyadic rationals are stored as records with a numerator and denominator.
\* The halving operator doubles the denominator, and the recursive normalizer
\* keeps the fraction reduced by dividing both fields by two whenever both are even.

CONSTANTS One, Half, Norm
CONSTANTS Specification, Init, Next, Invariants, Properties

VARIABLES val

vars == <<val>>

TypeOK ==
  /\ val \in [num : Integer, den : Integer]

Init ==
  /\ val = One

Next ==
  /\ \/ /\ val' = Half
        /\ TRUE
     \/ /\ val' = Norm(val)
        /\ TRUE

Spec == Specification

SpecDef == Specification == [vars |-> <<val>>] /\ Init /\ [][Next]_vars

Inv == Invariants

Props == Properties

\* One: the dyadic representation of the integer one.
OneDef == One = [num |-> 1, den |-> 1]

\* Half: an operator that halves a dyadic number by doubling its denominator.
HalfDef == Half == [num |-> val.num, den |-> val.den * 2]

\* Norm: recursively divides numerator and denominator by two while both are even.
NormDef ==
  Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
      THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
      ELSE p

====