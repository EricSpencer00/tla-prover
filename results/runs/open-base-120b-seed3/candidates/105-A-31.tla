---- MODULE DyadicRationals ----
EXTENDS Integers

\*--------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with integer
\* numerator `num` and integer denominator `den`.
\*--------------------------------------------------------------------
Dyadic == [num : Int, den : Int]

\* The dyadic rational representing the integer one.
One == [num |-> 1, den |-> 1]

\* Halving operation: multiplies the denominator by 2, leaving the
\* numerator unchanged.
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization recursively divides numerator and denominator by 2
\* while both are even.
RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

====