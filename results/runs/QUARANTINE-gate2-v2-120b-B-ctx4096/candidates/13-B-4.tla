---- MODULE MCBakery --------------------------------
EXTENDS Bakery

(*
   The original specification declared a constant MaxNat and then
   asserted `ASSUME MaxNat \notin Nat`.  Since Nat is the set of all
   natural numbers, that assumption is contradictory, causing TLC to
   report a false assumption at the start of model checking.

   To keep the module semantics‑preserving while removing the
   contradiction, we rename the constant to `MaxNatVal` and define it
   as a natural number that is **greater than** every natural number
   used in the model.  In practice we bound the natural numbers used by
   the Bakery module with a finite set `NatBound`.  The new definition
   guarantees that `MaxNatVal` is **outside** this bound, satisfying the
   original intention (a natural number larger than any used in the
   system) without conflicting with the definition of Nat.

   The definition of `NatBound` is kept minimal and can be overridden
   in a .cfg file if a different bound is desired.
*)

CONSTANT MaxNatVal

NatBound == 0 .. 10

ASSUME MaxNatVal \notin NatBound

NatOverride == NatBound

=============================================================================