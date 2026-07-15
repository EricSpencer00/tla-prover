---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants required by the reference configuration.
--------------------------------------------------------------------*)
CONSTANTS MaxNat, Nat

(*--------------------------------------------------------------------
  Derived definition: Nat is the finite set of natural numbers from 0
  up to MaxNat, inclusive.  This replaces the infinite ℕ used in the
  base proof with a bounded set that TLC can enumerate.
--------------------------------------------------------------------*)
Nat == 0..MaxNat

(*--------------------------------------------------------------------
  State variable: the natural number whose double we consider.
--------------------------------------------------------------------*)
VARIABLE n

(*--------------------------------------------------------------------
  Specification name expected by the configuration.
--------------------------------------------------------------------*)
SPECIFICATION Spec

(*--------------------------------------------------------------------
  Initial predicate: start with any value of n in the bounded set Nat.
--------------------------------------------------------------------*)
Init == n \in Nat

(*--------------------------------------------------------------------
  No actions are needed for checking the invariant; we define a stuttering
  action that leaves n unchanged and is always enabled.  This satisfies the
  requirement that a NEXT predicate be present.
--------------------------------------------------------------------*)
Next == UNCHANGED n

(*--------------------------------------------------------------------
  Safety invariant: the double of n is even.  An integer m is even iff
  there exists k with m = 2*k.  Since n is a natural number, 2*n is also
  natural.
--------------------------------------------------------------------*)
DoubleEven == \E k \in Nat : 2 * n = 2 * k

(*--------------------------------------------------------------------
  The overall specification combines the initial state with the temporal
  formula that repeatedly applies the Next action.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<n>>

(*--------------------------------------------------------------------
  The configuration expects the following names:
  - INVARIANTS: the set of safety invariants
  - PROPERTIES: the set of liveness or safety properties (empty here)
--------------------------------------------------------------------*)
INVARIANTS == DoubleEven
PROPERTIES == {}

====