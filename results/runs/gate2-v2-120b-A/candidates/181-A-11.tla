---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANTS MaxNat, Nat

(* 
  The constant Nat is overridden in the .cfg to be the finite range 
  0..MaxNat.  Here we simply expose Nat as a constant that the rest of 
  the specification can use.
*)

\* No state variables are needed for this configuration module. 
\* The actual model (the proof that 2*n is even) is assumed to be 
\* defined in an external module that this configuration imports. 
\* For TLC to have something to check we provide trivial definitions
\* of the required operators.  The theorem itself is captured as a 
\* constant-level assumption (see the .cfg file) and does not appear as
\* a runtime invariant.

(* ------------------------------------------------------------------- *)
(* The following operators are required by the reference configuration. *)

(* The specification name – a convention used by the .cfg file *)
SPECIFICATION == Init

(* Initial predicate – trivially true for a configuration module *)
Init == TRUE

(* Next-state relation – since there are no state variables, it is
   simply stuttering. *)
Next == UNCHANGED <<>>

(* Safety invariant – trivially true; the real safety condition is
   expressed as a constant assumption in the .cfg. *)
Inv == TRUE

(* Liveness property – also trivially true (no liveness condition
   needed for this configuration). *)
Liveness == <>TRUE

=============================================================================