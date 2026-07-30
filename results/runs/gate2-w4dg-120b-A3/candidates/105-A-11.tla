---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a rational number whose denominator is a power of two.
\* Operators: One (the value 1), Half (divide by two), and Norm (reduce an
\* even numerator and denominator by two, recursively).
\* TLC is configured with no required identifiers; this module is self-
\* contained and names every identifier the description asks for.

CONSTANTS num, den

RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

VARIABLES cur

TypeOK ==
    /\ cur \in [num : Int, den : Int]
    /\ cur.den >= 1
    /\ cur.den % 2 = 0

Init ==
    /\ cur = One

Next ==
    \/ cur' = Half(cur)
    \/ cur' = Norm(cur)

Spec == Init /\ [][Next]_cur

HalvesAreWellFormed == cur.den >= 1 /\ cur.den % 2 = 0

NormalizationEventuallyQuits == <>(cur = Norm(cur))

====