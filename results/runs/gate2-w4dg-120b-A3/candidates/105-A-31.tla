---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, OneHalf, Norm

\* A dyadic rational is a fraction whose denominator is a power of two.
\* The module has exactly the identifiers the description and the empty
\* .cfg file require: the constants below and the operators Spec, Init,
\* Next, Invs, and Props (the last two empty, because the config names
\* no invariants or properties).

VARIABLES p

vars == <<p>>

TypeOK == p \in [num : Nat, den : Nat]

Spec == One /\ Half /\ OneHalf /\ Norm

Init == p = One

Next == p' = [num |-> p.num, den |-> p.den * 2] \/ Norm(p)

Invs == TRUE

Props == TRUE

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

OneHalf == [num |-> 1, den |-> 2]

\* Recursively divide numerator and denominator by two while both are even;
\* the operation is guarded by the parity test so it always takes a step.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

====