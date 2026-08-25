---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite override for the infinite set Nat *)
NatOverride == 0 .. MaxNat

(* Evenness predicate using modular arithmetic for efficiency *)
Even(x) == x % 2 = 0

(* Assumed theorem: the double of any natural number is even *)
Theorem == \A m \in NatOverride : Even(2 * m)

(* Tell TLC to treat the theorem as a constant‑level assumption *)
ASSUME Theorem

====