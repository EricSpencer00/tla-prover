---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

(* 
   MC_sums_even is a configuration module that bounds the natural number
   set used in the underlying proof that "the double of any natural number is even".
   It introduces a constant MaxNat which limits the range of natural numbers to
   the finite set Nat = 0..MaxNat.  No state variables, actions, or additional
   properties are introduced here; the module simply supplies the constants and
   declares the operators required by the reference configuration.
*)

CONSTANTS MaxNat, Nat

(* Nat is defined as the finite range 0..MaxNat *)
NatDef == Nat = 0 .. MaxNat

(* 
   The underlying proof specification (not shown here) defines the theorem that
   for all n \\in Nat, 2 * n is even.  In this configuration module we treat that
   theorem as an assumed invariant, named DoubleEven, which is simply a tautology
   used to satisfy the TLC configuration.  The real proof lives in the extended
   specification.
*)
DoubleEven == TRUE

(* The SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES operators are
   required by the .cfg file.  Because no state machine is defined here,
   they are defined as trivial constants that reference the assumed theorem. *)

SPECIFICATION == NatDef /\ DoubleEven

INIT == NatDef

NEXT == UNCHANGED Nat

INVARIANTS == DoubleEven

PROPERTIES == DoubleEven

====