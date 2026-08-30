---- MODULE MC_sums_even ----
EXTENDS Naturals

(* A model-checking configuration module for the proof that the double of any    *)
(* natural number is even.  It extends the main proof specification and        *)
(* overrides the natural number set to a finite range so TLC can check it.     *)

CONSTANT MaxNat

(* The overridden NAT set is a bounded (finite) version of the naturals.  The  *)
(* standard NAT operator from Naturals is replaced here.                        *)
NatOverride == 0..MaxNat

(* The theorem that for every natural number n, 2*n is even, is assumed as a    *)
(* constant-level assumption for these bounded checks.                         *)
Theorem == \A n \in NatOverride : (2 * n) % 2 = 0

Spec == Theorem

Init == Spec

Next == Spec

TypeOK == TRUE

SpecOK == Spec

====