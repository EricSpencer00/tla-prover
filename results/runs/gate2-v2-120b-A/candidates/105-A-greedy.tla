---- MODULE DyadicRationals ----
EXTENDS Integers

(*-----------------------------------------------------------------
  Dyadic rational numbers are represented as records with two fields:
    - num : integer numerator
    - den : positive integer denominator (a power of two)
  The module defines:
    * One   : the dyadic rational 1/1
    * Half  : the dyadic rational 1/2
    * Norm  : a recursive normalization operator that divides both
             numerator and denominator by 2 while both are even.
-----------------------------------------------------------------*)

VARIABLES p

(*--- Constants (record values) -----------------------------------*)
One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

(*--- Helper predicate: both components are even -------------------*)
BothEven(q) == /\ q.num % 2 = 0
               /\ q.den % 2 = 0

(*--- Normalization operator ---------------------------------------*)
Norm(q) == IF BothEven(q)
            THEN Norm([num |-> q.num \div 2,
                       den |-> q.den \div 2])
            ELSE q

(*--- Initial state ------------------------------------------------*)
Init == p = One

(*--- Next-state relation ------------------------------------------*)
Next == p' = Norm([num |-> p.num,
                   den |-> p.den * 2])

(*--- Specification (temporal formula) ----------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*--- Optional: a simple invariant stating that the denominator
      is always a positive power of two. ---------------------------*)
DenIsPowerOfTwo == p.den > 0 /\ \A i \in 1..p.den : (i % 2 = 0) => (p.den % i = 0) => (i = p.den)

=============================================================================