---------------------------- MODULE MCBakery --------------------------------
EXTENDS Bakery
CONSTANT MaxNat

(* 
  We replace the contradictory assumption with a correctly typed one.
  The original assumption `MaxNat \notin Nat` makes the model
  uninstantiable because `Nat` (the natural numbers) is the only
  possible value for a constant that is used as a bound of an interval.
  The intention of the original author was to state that `MaxNat` is a
  natural number used as the upper bound of the interval `NatOverride`.
  Therefore we assert that `MaxNat` belongs to the natural numbers.
*)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================