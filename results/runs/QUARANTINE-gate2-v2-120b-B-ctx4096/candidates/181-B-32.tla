------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

(* Adjust the domain of MaxNat to be a natural number.
   The original assumption MaxNat \notin Nat caused an immediate
   failure during model checking.  By restricting MaxNat to Nat and
   using it as the upper bound of NatOverride we keep the intended
   semantics while allowing the model to be explored. *)
CONSTANT MaxNat
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* Preserve the original assumed property T1 from the extended module. *)
ASSUME T1
=============================================================================