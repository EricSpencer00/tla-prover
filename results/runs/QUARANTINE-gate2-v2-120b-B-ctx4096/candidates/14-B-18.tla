---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* Assume MaxNat is a natural number that is *greater* than the biggest
   number allowed in the original module's Nat set.  The original
   specification used the (incorrect) assertion that MaxNat is *not* a
   natural number, which makes the model trivially inconsistent.  The
   corrected assumption states the intended relationship without
   weakening the intended invariant. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
====