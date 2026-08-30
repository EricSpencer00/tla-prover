---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm
RECURSIVE RecNorm(_)
RecNorm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN RecNorm([num |-> p.num \div 2, den |-> p.den \div 2])
                                   ELSE p

VARIABLES p
vars == <<p>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 1, den |-> 2]

Init ==
    /\ p = One

DoubleDen ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

HalfStep ==
    /\ p' = Half

Normalize ==
    /\ p' = RecNorm(p)

Next ==
    \/ DoubleDen
    \/ HalfStep
    \/ Normalize

Spec == Init /\ [][Next]_vars

RationalForm == DenominatorIsPowerOfTwo(p) /\ p.num % 2 # 0 \/ p.den = 2 ^ (LogBase(2, p.den)

====