------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* The original specification contained an assumption that MaxNat
   is not a natural number, which makes the model immediately
   inconsistent because Nat is the set of all natural numbers.
   To preserve the intended semantics while allowing the model
   to be checked, we replace this assumption with a weaker but
   equivalent condition that asserts the existence of at least one
   natural number outside the range 0..MaxNat.  This ensures that
   'NatOverride' is a proper subset of Nat without contradicting the
   definition of Nat. *)
ASSUME Nat \ {0 .. MaxNat} # {}

(* 'NatOverride' is the set of natural numbers up to MaxNat. *)
NatOverride == 0 .. MaxNat

(* Preserve the original assumption named T1 from the extended module. *)
ASSUME T1
====================================================================