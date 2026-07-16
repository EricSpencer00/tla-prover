---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* The original specification asserted that MaxNat is not a natural number
   (Nat), which makes the subsequent definition NatOverride empty and the
   invariant StateConstraint trivially true.  In practice, MaxNat is intended
   to be a natural bound for the counters in the Boulanger module, so we
   require that it be a natural number.  This change preserves the intended
   meaning of the module while making the assumption satisfiable. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====