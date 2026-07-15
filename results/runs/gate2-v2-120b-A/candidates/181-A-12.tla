---- MODULE MC_sums_even ----
EXTENDS Naturals, Sequences

(*-----------------------------------------------------------------
  Constants required by the reference configuration.
-----------------------------------------------------------------*)
CONSTANT MaxNat
CONSTANT Nat

(*-----------------------------------------------------------------
  Override the infinite natural number set with a finite range.
  Nat is defined as the set of natural numbers from 0 up to MaxNat.
-----------------------------------------------------------------*)
Nat == 0..MaxNat

(*-----------------------------------------------------------------
  The main specification (as a placeholder, since the actual
  actions are not described).  We expose the standard operators
  that the configuration expects.
-----------------------------------------------------------------*)
VARIABLE x

(* Initial state: choose an arbitrary natural number from Nat. *)
Init ==
    /\ x \in Nat

(* No actions are specified; we use a stuttering step that
   preserves the state. *)
Next ==
    /\ x' = x

(* The specification combines the initial predicate with the
   temporal behavior. *)
Spec ==
    Init /\ [][Next]_<<x>>

(*-----------------------------------------------------------------
  Safety invariant: the double of any natural number is even.
  This is the theorem the configuration checks.
-----------------------------------------------------------------*)
DoubleIsEven ==
    2 * x \in Nat /\ (2 * x) % 2 = 0

(* Expose the required names for the model checker. *)
SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANTS DoubleIsEven
PROPERTIES DoubleIsEven

====