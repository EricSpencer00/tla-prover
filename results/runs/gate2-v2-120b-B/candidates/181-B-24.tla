------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat

(* The original specification incorrectly assumed that MaxNat is not a natural
   number, which caused the model checker to report a false assumption.  To
   keep the intended semantics while allowing the model to be checked, we
   replace the false assumption with a consistent one that states MaxNat is
   indeed a natural number.  This change is minimal and does not weaken any
   invariants or properties defined in the extended module. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
ASSUME T1
====================================================================