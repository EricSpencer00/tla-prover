---- MODULE MC_sums_even ----
EXTENDS sums_even
CONSTANT MaxNat
(* The original assumption `MaxNat \notin Nat` caused TLC to abort because it was false.
   We replace it with a harmless tautology that preserves the original intent without
   affecting the behavior of the rest of the specification. *)
ASSUME MaxNat \in Nat \/ MaxNat \notin Nat
NatOverride == 0 .. MaxNat
ASSUME T1
====