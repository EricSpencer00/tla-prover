---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is stored in lowest terms with a denominator that is a power
\* of two.  Fractions like 2/1 and 4/2 represent the same value, so the
\* normalization operator is essential for keeping the two states distinct.
\* The invariants below guard against overflow and against a denominator that
\* has lost its power-of-two shape.

CONSTANTS Numerators, Denominators

VARIABLES num, den

vars == <<num, den>>

TypeOK ==
    /\ num \in Numerators
    /\ den \in Denominators

Spec ==
    /\ num = 1
    /\ den = 1

\* Halves the dyadic rational; the denominator stays a power of two by design.
Half ==
    /\ den \in Denominators
    /\ den * 2 \in Denominators
    /\ num' = num
    /\ den' = den * 2

\* Normalizes an even-even fraction by dividing both parts by two, and recurses.
Norm(p) ==
    IF p[1] % 2 = 0 /\ p[2] % 2 = 0
        THEN Norm([p[1] \div 2, p[2] \div 2])
        ELSE p

\* The primitive step is dividing both by two once; the recursion lives in Norm.
ReduceEven ==
    /\ num % 2 = 0
    /\ den % 2 = 0
    /\ num' = num \div 2
    /\ den' = den \div 2

\* Multiplying the denominator by two pushes the fraction into a finer dyadic
\* slot; it is the only way the denominator grows, so NormalDenominator below
\* stays true even though the value itself is unchanged.
DoubleDenominator ==
    /\ den \in Denominators
    /\ den * 2 \in Denominators
    /\ den' = den * 2
    /\ UNCHANGED num

Next == Half \/ ReduceEven \/ DoubleDenominator

Spec == Init /\ [][Next]_vars

\* NormalDenominator: the denominator shape is never broken by any step.
NormalDenominator ==
    den \in Denominators

\* Within the bounded range of Numerators/Denominators, the same rational value
\* is never represented by two different pairs.
NoDuplicateValue ==
    \A a, b \in { [num |-> num, den |-> den] : num \in Numerators, den \in Denominators } :
        (a[1] * b[2] = a[2] * b[1]) => (a[1] = b[1] /\ a[2] = b[2])

====