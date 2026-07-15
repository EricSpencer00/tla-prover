---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets, Sequences

(* ----------------------------------------------------------------------
   Configuration module for checking the theorem that "the double of any
   natural number is even".  This module overrides the infinite set of
   naturals with a finite bounded range and imports the definitions from
   the base proof module (which we model here directly for completeness).
   ---------------------------------------------------------------------- *)

CONSTANT MaxNat

(* Nat is the finite set {0, 1, ..., MaxNat} *)
Nat == 0 .. MaxNat

VARIABLES x

(* Initial state: choose any natural number in the bounded range. *)
Init == 
    /\ x \in Nat

(* Action: compute the double of the current number.  No state change,
   but the action exists so that TLC has a NEXT relation. *)
Next == 
    /\ x \in Nat
    /\ UNCHANGED x

(* For completeness, define the main specification as the temporal
   formula that starts with Init and repeatedly executes Next. *)
Spec == Init /\ [][Next]_<<x>>

(* Safety property: the double of any natural number is even. *)
EvenDouble == (2 * x) % 2 = 0

(* Liveness/property placeholders – the base spec does not provide any. *)
NoLiveness == TRUE

=============================================================================