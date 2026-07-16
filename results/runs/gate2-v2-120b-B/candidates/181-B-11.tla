---- MODULE MC_sums_even ----
EXTENDS sums_even

(* Declare MaxNat as a constant that can be any natural number, including 0. *)
CONSTANT MaxNat

(* No need for an explicit ASSUME on MaxNat; TLC will assign values via the .cfg file. *)

(* Override the Nat set from sums_even to be the finite range 0..MaxNat
   for the model checking run. *)
NatOverride == 0 .. MaxNat

(* Keep the original assumption T1 from the sums_even module. *)
ASSUME T1
====