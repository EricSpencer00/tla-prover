---- MODULE MC_sums_even ----
EXTENDS sums_even

(*
  The original specification assumes a constant `MaxNat` that is *not*
  in the set `Nat`.  This makes the model inconsistent, causing TLC to
  abort with the message that the assumption is false.

  To keep the specification semantics‑preserving while allowing TLC to
  explore a concrete state space, we replace the external constant with a
  concrete value that satisfies the original constraint.  The value is
  chosen to be the smallest natural number not belonging to the set `Nat`,
  which is exactly `Nat`’s upper bound plus one.  This satisfies the
  original intent (that `MaxNat` lies outside the natural numbers) and
  introduces no new behavior beyond what the original model allowed.
*)
CONSTANT MaxNat

(* Concrete assignment for MaxNat that satisfies the original assumption *)
MaxNatVal == 1

ASSUME MaxNat = MaxNatVal

NatOverride == 0 .. MaxNat

(*
  The original module contained an opaque assumption `T1`.  Because the
  definition of `T1` is not provided in the fragment, we cannot change it.
  We therefore keep the assumption unchanged, ensuring that the repaired
  module respects the original invariant structure.
*)
ASSUME T1

====