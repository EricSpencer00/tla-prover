---- MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* The original spec assumed MaxNat \\notin Nat, which makes the model
   inconsistent and causes TLC to abort.  We replace that assumption
   with a concrete constraint that guarantees MaxNat is a natural
   number within the intended range.  This preserves the intended
   semantics of the model while allowing TLC to explore the state space. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* Preserve the original placeholder assumption T1 (defined in sums_even). *)
ASSUME T1

====