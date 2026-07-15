---- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger

CONSTANT MaxNat

(* A well‑formedness condition on MaxNat: it must be a natural number. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs :
    num[process] < MaxNat
=============================================================================