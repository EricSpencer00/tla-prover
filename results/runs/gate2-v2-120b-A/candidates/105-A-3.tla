---- MODULE DyadicRationals ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (not assigned values here; they will be given in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT One
CONSTANT Half
CONSTANT Norm

\* ----------------------------------------------------------------------
\* Record definition for dyadic rationals
\* ----------------------------------------------------------------------
Dyadic == [num : Nat, den : Nat]

\* ----------------------------------------------------------------------
\* Helper predicate: both numerator and denominator are even
\* ----------------------------------------------------------------------
BothEven(p) == (p.num % 2 = 0) /\ (p.den % 2 = 0)

\* ----------------------------------------------------------------------
\* Recursive normalization operator (as described)
\* ----------------------------------------------------------------------
Norm(p) ==
    IF BothEven(p) THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE
        p

\* ----------------------------------------------------------------------
\* Halving operator (adds a factor of 2 to the denominator)
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Initial state: the dyadic rational representing one (1/1)
\* ----------------------------------------------------------------------
Init == One = [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* State variable representing the current dyadic rational
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Initial predicate for the state variable
\* ----------------------------------------------------------------------
VARIABLES p
Init == p = One

\* ----------------------------------------------------------------------
\* Next-state relation: either halve or normalize
\* ----------------------------------------------------------------------
Next == 
    \/ p' = Half(p)
    \/ p' = Norm(p)

\* ----------------------------------------------------------------------
\* Specification (temporal formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_p

\* ----------------------------------------------------------------------
\* Invariant: denominator is always a positive power of two
\* (ensures the normalization never yields a denominator that is zero)
\* ----------------------------------------------------------------------
DenIsPowerOfTwo == \A n \in Nat : (p.den = 2 ^ n)

\* ----------------------------------------------------------------------
\* Property: the value represented by p is always between 0 and 2 (inclusive)
\* ----------------------------------------------------------------------
Value(p) == p.num / p.den
Bounded == Value(p) \in 0..2

=============================================================================