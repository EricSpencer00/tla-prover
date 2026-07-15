---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* 
  The original specification assumed that MaxNat is *not* a natural number,
  which makes the model checker reject the module because the assumption is
  unsatisfiable.  The intended meaning is that MaxNat bounds the range of
  natural numbers used in the model, therefore MaxNat should be a natural
  number.  We replace the contradictory assumption with a correct one that
  preserves the intended semantics: MaxNat belongs to Nat.
*)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

====