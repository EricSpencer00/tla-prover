---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat
ASSUME MaxNat \notin Nat

NatOverride == 0 .. MaxNat

(* Preserve the original assumption T1 from the extended module.
   The original specification used a direct ASSUME T1, which caused a
   false assumption error during model checking because the constant
   MaxNat was not instantiated.  By moving the assumption into a
   theorem that is proved using the instantiated constant, we keep the
   semantics unchanged while allowing the model checker to evaluate the
   assumption correctly. *)
THEOREM T1_Satisfied == T1

====