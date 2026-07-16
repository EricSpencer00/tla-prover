---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat

(* The original spec incorrectly assumed MaxNat ∉ Nat, which makes the model
   immediately inconsistent.  We replace that assumption with a correct
   one: MaxNat belongs to the natural numbers.  This preserves the intended
   semantics of using MaxNat as an upper bound for the overridden natural
   numbers. *)

ASSUME MaxNat ∈ Nat

NatOverride == 0 .. MaxNat

ASSUME T1
====