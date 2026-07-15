---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Dyadic rationals are represented as records with two fields:
    - num : natural number (the numerator)
    - den : natural number (the denominator, a power of two)
  The set of all such records is called Dyadic.
-----------------------------------------------------------------*)
Dyadic == { [num |-> n, den |-> d] : n \in Nat, d \in Nat \ {0} }

(*-----------------------------------------------------------------
  One : the dyadic representation of the rational number 1.
-----------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]

(*-----------------------------------------------------------------
  Half : a dyadic number that represents one half.
-----------------------------------------------------------------*)
Half == [num |-> 1, den |-> 2]

(*-----------------------------------------------------------------
  Norm : recursive normalization that removes common factors of 2.
  If both numerator and denominator are even, divide each by 2 and
  recurse; otherwise return the record unchanged.
-----------------------------------------------------------------*)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  Init : the initial state of the system (one dyadic rational: One).
-----------------------------------------------------------------*)
Init == One

(*-----------------------------------------------------------------
  Next : nondeterministically either keep the current state or replace
  it with its normalized form. This models the ability to apply
  normalization repeatedly.
-----------------------------------------------------------------*)
Next == 
  \/ p' = p
  \/ p' = Norm(p)

(*-----------------------------------------------------------------
  Spec : the overall specification, stating that the system starts in
  Init and repeatedly executes Next.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*-----------------------------------------------------------------
  Invariant stating that the denominator of any reachable state is a
  power of two. This captures the essential property of dyadic rationals.
-----------------------------------------------------------------*)
IsPowerOfTwo(d) == \E k \in Nat : d = 2^k

DenIsPowerOfTwo == IsPowerOfTwo(p.den)

(*-----------------------------------------------------------------
  Property guaranteeing that normalization never changes the represented
  rational value. For any reachable state, the rational value of p
  equals that of its normalized form.
-----------------------------------------------------------------*)
RationalValue(p) == p.num / p.den

NormPreservesValue == p.num / p.den = Norm(p).num / Norm(p).den

=============================================================================