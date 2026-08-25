---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite override for the infinite set Nat *)
NatOverride == 0 .. MaxNat

(* Evenness predicate using the finite NatOverride *)
Even(x) == \E y \in NatOverride : x = 2 * y

(* Assumed theorem: the double of any natural number is even *)
Theorem == \A m \in NatOverride : Even(2 * m)

(* Tell TLC to treat the theorem as a constant‑level assumption *)
ASSUME Theorem

====