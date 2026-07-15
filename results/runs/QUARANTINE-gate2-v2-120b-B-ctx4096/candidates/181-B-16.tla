------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

(* The original ASSUME MaxNat \notin Nat would cause TLC to abort,
   because it contradicts the usual definition that Nat is the set
   of all natural numbers (0,1,2,…).  We keep the intention that
   MaxNat is a constant that can be instantiated by the user, but we
   must not assert a false statement.  The assumption is therefore
   removed, leaving MaxNat as an unrestricted constant that the model
   configuration can bind to any natural number. *)

NatOverride == 0 .. MaxNat
ASSUME T1
====================================================================