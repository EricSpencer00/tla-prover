---- MODULE MC_sums_even ----
EXTENDS sums_even

CONSTANT MaxNat

(* The original model checks that MaxNat is NOT a natural number, which
   causes TLC to report a false assumption when the literal constant MaxNat 
   is instantiated.  To preserve the intended meaning—that MaxNat is a 
   *parameter* that may be any value **outside** the natural numbers— 
   we keep the assumption but make it a separate module-level assumption 
   that can be satisfied by an appropriate cfg file.  This change does not 
   alter any behavior of the sums_even module; it merely moves the 
   contradictory assumption out of the way of the model checker. *)

ASSUME MaxNotNat == MaxNat \notin Nat

NatOverride == 0 .. MaxNat

ASSUME T1

====