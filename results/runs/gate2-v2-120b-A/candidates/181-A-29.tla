---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS MaxNat, Nat

(*-----------------------------------------------------------------
  Assumptions (derived from the description)
-----------------------------------------------------------------*)
(* Nat is the set of natural numbers from 0 up to MaxNat inclusive. *)
NatAssumption == Nat = 0..MaxNat

(* The finite bound for model checking is MaxNat = 1_000_000. *)
MaxNatAssumption == MaxNat = 1000000

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLE x

(*-----------------------------------------------------------------
  Definitions
-----------------------------------------------------------------*)
(* The set of all natural numbers (finite, bounded by MaxNat). *)
NatSet == Nat

(* State predicate: x is always a natural number in the bounded set. *)
State == x \in NatSet

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init == 
    /\ NatAssumption
    /\ MaxNatAssumption
    /\ x = 0

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next == 
    /\ x' = x + 1
    /\ x' \in NatSet

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<x>>

(*-----------------------------------------------------------------
  Safety invariant: the double of any natural number in the state is even.
-----------------------------------------------------------------*)
EvenDouble == (2 * x) % 2 = 0

(*-----------------------------------------------------------------
  Configuration placeholders (required identifiers)
-----------------------------------------------------------------*)
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANTS    == EvenDouble
PROPERTIES    == EvenDouble

=============================================================================