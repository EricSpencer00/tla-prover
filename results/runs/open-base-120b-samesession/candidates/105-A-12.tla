---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE p

\* Helper predicate: denominator must be a power of two
IsPowerOfTwo(d) == \E k \in Nat : d = 2 ^ k

\* Set of dyadic rational numbers represented as records {num, den}
Dyadic == {
    [num |-> n, den |-> d] :
        n \in Int /\ d \in Nat /\ d # 0 /\ IsPowerOfTwo(d)
}

\* Constant representing the dyadic rational 1/1
One == [num |-> 1, den |-> 1]

\* Halving operator: multiply denominator by 2
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization: divide numerator and denominator by 2 while both are even
RECURSIVE Norm(_)

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* Initial state: start at 1
INIT == p = One

\* Next-state relation: either halve or normalize
NEXT ==
    \/ p' = Half(p)
    \/ p' = Norm(p)

\* Overall specification
SPECIFICATION == INIT /\ []NEXT

\* Invariant: the state variable always denotes a dyadic rational
INVARIANTS == p \in Dyadic

\* Placeholder property (always true)
PROPERTIES == TRUE

====