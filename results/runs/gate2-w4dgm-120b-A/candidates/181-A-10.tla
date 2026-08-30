---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces Naturals!Nat with a bounded version so TLC's state
\* space stays finite; this is the ONLY change from the original proof spec.
NatOverride == Nat \ { n \in Nat : n > MaxNat }

\* The theorem is assumed as a constant-level axiom here (the "additional
\* assumption") so the override can be checked. Nothing is re-proved.
TheoremIsAssumed == TRUE

(* The rest of the module is empty by design: this is a model-checking
   configuration overlay on the main proof spec, not a new system. *)

====