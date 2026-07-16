---- MODULE MCBakery -------------------------------------------------
EXTENDS Bakery

(* 
  The original specification declared a constant MaxNat and introduced an
  (incorrect) assumption that MaxNat ∉ Nat.  Since Nat is the set of all
  natural numbers, this assumption can never hold and causes TLC to reject
  the model immediately.  The intention of the module is to provide a
  bounded set of natural numbers that the underlying Bakery module can use.
  To achieve that, we keep MaxNat as a constant and define NatOverride as the
  set of natural numbers up to (and including) MaxNat, without imposing an
  impossible assumption.
*)
CONSTANT MaxNat

NatOverride == 0 .. MaxNat

=============================================================================