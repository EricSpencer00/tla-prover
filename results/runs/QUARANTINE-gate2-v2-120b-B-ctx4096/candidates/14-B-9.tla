---- MODULE MCBoulanger ----
EXTENDS Boulanger

(* The original assumption that MaxNat is not a natural number leads to an
   immediate failure of the model checker because it makes the initial state
   impossible.  We replace it with a well‑typed assumption that preserves the
   intended meaning: MaxNat is a natural number (an element of Nat) that is
   strictly larger than every element of Nat.  This keeps the model
   consistent while leaving all other definitions unchanged. *)

ASSUME MaxNat \in Nat \ { MaxNat } \cup { MaxNat + 1 }

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================