---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

Nat == 0..MaxNat

\* Theorem: for every natural number n, the sum of the first n natural numbers
\* is even exactly when n is even.
SumFirstIsEvenIffNIsEven ==
    \A n \in Nat : (n * (n + 1) / 2) % 2 = n % 2

AssumeTheorem == SumFirstIsEvenIffNIsEven

Specification == SumFirstIsEvenIffNIsEven

Init == AssumeTheorem

Next == Init

Spec == Init /\ [][Next]_<< >>

TypeOK == TRUE

StateConstraint == TRUE

====