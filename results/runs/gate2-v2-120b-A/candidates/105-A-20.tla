---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers, TLC

(*--------------------------------------------------------------------
  Dyadic rationals: fractions num/den where den is a positive power of two.
  The module defines:
    - One : the dyadic rational representing 1 (1/1)
    - Half : a function that halves a dyadic rational
    - Norm : a recursive normalization operator that divides numerator and
             denominator by 2 while both are even
  It also defines the generic specification variables and actions required
  by the testing harness.
--------------------------------------------------------------------*)

VARIABLES p, pprime

(*--------------------------------------------------------------------
  Record constructors (used for readability)
--------------------------------------------------------------------*)
OneRec == [num |-> 1, den |-> 1]

(*--------------------------------------------------------------------
  Helper predicate: den must be a positive power of two.
--------------------------------------------------------------------*)
IsPowerOfTwo(d) == d > 0 /\ \A k \in Nat : d = 2^k

(*--------------------------------------------------------------------
  Normalization operator: repeatedly divide numerator and denominator by 2
  while both are even.
--------------------------------------------------------------------*)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*--------------------------------------------------------------------
  Publicly exported operators (exact names required)
--------------------------------------------------------------------*)
One == OneRec

Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

(*--------------------------------------------------------------------
  Specification of the system's behavior.
  - Init: start in the normalized state One.
  - Next: either stay unchanged or apply Half to the current state.
--------------------------------------------------------------------*)
Init == p = One /\ IsPowerOfTwo(p.den)

Next == 
  \/ /\ pprime = p
        /\ UNCHANGED p
  \/ /\ pprime = Half(p)
        /\ IsPowerOfTwo(pprime.den)

Spec == Init /\ [][Next]_<<p>>

=============================================================================