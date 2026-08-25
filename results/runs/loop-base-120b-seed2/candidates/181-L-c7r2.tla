---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* NatOverride replaces Nat with a finite version for model checking *)
NatOverride == 0 .. MaxNat

VARIABLES n

(* Initial predicate: n ranges over the finite natural numbers *)
Init == n \in NatOverride

(* Stutter step – the system does nothing; this keeps the model simple
   while still satisfying the shape required by TLC. *)
Next == n' = n

(* Full specification used by TLC when no explicit INIT/NEXT are given
   in the configuration file. *)
Spec == Init /\ [][Next]_<<n>>

=============================================================================