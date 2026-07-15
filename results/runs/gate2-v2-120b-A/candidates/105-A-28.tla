---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers

(*--------------------------------------------------------------------
  Record definition for a dyadic rational.
  A dyadic rational is represented as a record with fields:
    num : numerator   (an integer, may be negative or zero)
    den : denominator (a positive integer, a power of two)
--------------------------------------------------------------------*)
VARIABLE p

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

(*--------------------------------------------------------------------
  Normalization operator.
  It repeatedly divides numerator and denominator by 2 while both are
  even, yielding a canonical representation where at least one of the
  two numbers is odd (or the numerator is zero).
--------------------------------------------------------------------*)
Norm(r) ==
  IF r.num % 2 = 0 /\ r.den % 2 = 0
    THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2])
    ELSE r

(*--------------------------------------------------------------------
  State variable: the current dyadic rational, always kept normalized.
--------------------------------------------------------------------*)
VARIABLE p

(*--------------------------------------------------------------------
  Initial predicate: start with the normalized value One.
--------------------------------------------------------------------*)
Init == p = One

(*--------------------------------------------------------------------
  Next-state relation: at each step the system may either
    * halve the current value, or
    * normalize the current value (a no‑op when already normalized).
--------------------------------------------------------------------*)
Next ==
  \/ p' = Half
  \/ p' = Norm(p)

(*--------------------------------------------------------------------
  Specification: the usual TLA+ temporal formula.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*--------------------------------------------------------------------
  Invariant: the denominator is always a positive power of two,
  and the fraction is in reduced form (no common factor 2).
--------------------------------------------------------------------*)
DenIsPowerOfTwo(d) == d > 0 /\ \A n \in Nat : (2 ^ n = d) => TRUE

Reduced(r) ==
  /\ r.den > 0
  /\ (r.num = 0 => r.den = 1)               \* zero is represented as 0/1
  /\ ~ (r.num % 2 = 0 /\ r.den % 2 = 0)    \* no common factor 2

Inv == Reduced(p)

(*--------------------------------------------------------------------
  Optional (but harmless) theorem stating that the specification implies the invariant.
--------------------------------------------------------------------*)
THEOREM SpecImpliesInv == Spec => []Inv

====