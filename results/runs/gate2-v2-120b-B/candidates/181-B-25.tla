------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even

CONSTANT MaxNat

(* MaxNat must be a natural number (or infinity) to keep NatOverride non‑empty *)
ASSUME NatOverride /= {}

NatOverride == 0 .. MaxNat

(* Preserve original assumption that some property T1 holds in the extended module *)
ASSUME T1

=============================================================================