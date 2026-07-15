---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS MaxNat, Nat

(*-----------------------------------------------------------------
  Finite range for Nat (overridden in the .cfg file)
-----------------------------------------------------------------*)
NatRange == 0 .. MaxNat

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLE n, double

(*-----------------------------------------------------------------
  Initial state: choose a natural number n in the bounded range,
  compute its double.
-----------------------------------------------------------------*)
Init ==
    /\ n \in NatRange
    /\ double = 2 * n

(*-----------------------------------------------------------------
  Stuttering next action: keep n and double unchanged.
  The system is otherwise inert; we only need Init for TLC.
-----------------------------------------------------------------*)
Next ==
    UNCHANGED <<n, double>>

(*-----------------------------------------------------------------
  Specification (temporal formula)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<n, double>>

(*-----------------------------------------------------------------
  Safety invariant: the computed double is always even.
-----------------------------------------------------------------*)
EvenDouble == double % 2 = 0

(*-----------------------------------------------------------------
  Theorem assumed as a constant-level assumption for TLC.
  It asserts that for every n in NatRange, 2*n is even.
-----------------------------------------------------------------*)
EvenTheorem == \A n \in NatRange : (2 * n) % 2 = 0

(*-----------------------------------------------------------------
  Exported identifiers required by the .cfg file
-----------------------------------------------------------------*)
THEOREM EvenTheorem
INVARIANT EvenDouble
SPECIFICATION Spec

====