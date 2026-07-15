------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

(* Ensure that MaxNat is an element of Nat, i.e., a natural number. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

(* Prevent a circular dependency by assuming T1 is true only if it does not
   refer to MaxNat; otherwise, the assumption is vacuous. *)
ASSUME \E x \in Nat : x = MaxNat => T1

====================================================================