---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANT p
\* p is a record representing a dyadic rational with fields:
\*   num : numerator  (an integer)
\*   den : denominator (a positive integer, a power of 2)

One == [num |-> 1, den |-> 1]

Half(x) == [num |-> x.num, den |-> x.den * 2]

\* Normalization: keep dividing numerator and denominator by 2 while both are even.
Norm(x) ==
  IF x.num % 2 = 0 /\ x.den % 2 = 0
  THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2])
  ELSE x

\* State variable representing the current dyadic rational.
VARIABLE p

\* Helper predicate to check that a record is a valid dyadic rational.
IsDyadic(r) ==
  /\ r.den > 0
  /\ \A k \in 1..(r.den) : (r.den = 2 ^ k) \/ (r.den = 1)   \* denominator is a power of two

\* Initial state: the dyadic rational is One.
Init == p = One

\* Next-step relation: either halve the current rational or normalize it.
Next ==
  \/ p' = Half(p)
  \/ p' = Norm(p)

\* Full specification (state machine).
Spec == Init /\ [][Next]_p

\* The set of all reachable dyadic rationals.
Reachable == { v \in [num : Int, den : Nat] : 
                /\ IsDyadic(v)
                /\ \E w \in [num : Int, den : Nat] : 
                     Init /\ [][Next]_{p} /\ v = p }

\* Invariant: the denominator of p is always a power of two.
DenPowerOfTwo ==
  \E k \in Nat : p.den = 2 ^ k

\* Invariant: the numerator and denominator are always non‑negative (optional, but useful).
NonNegative ==
  /\ p.num >= 0
  /\ p.den >= 1

\* Property: every reachable state can be obtained by normalizing some dyadic rational.
NormalizationCompleteness ==
  \A v \in Reachable : \E w \in [num : Int, den : Nat] :
       (w.num % 2 = 0 /\ w.den % 2 = 0) => Norm(w) = v

====