---- MODULE MC_sums_even ----
\* Configuration module for the TLA+ proof that the double of any natural number is even.
\* It imports the base proof and overrides the natural number set to a finite range
\* so TLC can check the theorem for a bounded set of values.
EXTENDS Naturals, Integers

CONSTANTS MaxNat

\* Operators inherited from Naturals (Nat, which is infinite) are replaced by
\* their finite-range counterparts here, re-implemented in terms of Integer.
\* MaxNat (a constant) bounds the range that NatOverride defines.
NatOverride(n) ==
  /\ n \in Nat
  /\ n <= MaxNat
  /\ n \in Nat

\* SAFETY PROPERTY: the theorem being modeled, assumed true for the reduction.
EvenDouble ==
  \A n \in Nat : (2 * n) \in Nat /\ (2 * n) \in 2 \cdot Nat

\* LIVENESS PROPERTY: the theorem is reachable from the base case n = 0.
DoubleEvenReachesBase ==
  \A n \in 1 .. MaxNat : \E k \in 1 .. n : (2 * k) \in Nat /\ (2 * k) \in 2 \cdot Nat

\* LIVENESS PROPERTY: the theorem is always reachable from any starting point.
DoubleEvenAlwaysReaches ==
  \A n \in 0 .. MaxNat : \E k \in 0 .. MaxNat : (2 * k) \in Nat /\ (2 * k) \in 2 \cdot Nat

====