---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  MC_sums_even
  Model-checking configuration module for the theorem:
      The double of any natural number is even.
  It overrides the infinite Nat set with a finite bounded range.
--------------------------------------------------------------------*)

CONSTANT MaxNat, Nat

(*--------------------------------------------------------------------
  State variables (none required for the invariant test)
--------------------------------------------------------------------*)
VARIABLES dummy

(*--------------------------------------------------------------------
  Safety invariant: Every element of Nat has an even double.
  This is the theorem we want TLC to check.
--------------------------------------------------------------------*)
EvenDoubles == \A n \in Nat : (2 * n) % 2 = 0

(*--------------------------------------------------------------------
  Initial state (trivial, does not affect the invariant)
--------------------------------------------------------------------*)
Init == dummy = 0

(*--------------------------------------------------------------------
  Next-state relation (trivial stuttering)
--------------------------------------------------------------------*)
Next == UNCHANGED dummy

(*--------------------------------------------------------------------
  Specification (temporal formula)
--------------------------------------------------------------------*)
SPECIFICATION == Init /\ [][Next]_<<dummy>>

(*--------------------------------------------------------------------
  INVARIANTS and PROPERTIES required by the .cfg file
--------------------------------------------------------------------*)
INVARIANTS == EvenDoubles
PROPERTIES == EvenDoubles

=============================================================================