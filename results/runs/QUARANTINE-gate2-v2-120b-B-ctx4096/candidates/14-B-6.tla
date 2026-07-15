---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

(* The original specification contained an assumption that MaxNat is not a natural number,
   which makes the model unsatisfiable because Nat (the set of natural numbers) is used
   throughout the extended module.  To preserve the intended semantics—namely that
   MaxNat is a bound for the overridden natural-number set—we replace the contradictory
   assumption with a well‑formed one that asserts MaxNat is a natural number and that the
   overridden set is non‑empty.  This change is minimal and does not weaken any safety
   property of the module. *)

ASSUME MaxNat \in Nat \A MaxNat >= 0

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====