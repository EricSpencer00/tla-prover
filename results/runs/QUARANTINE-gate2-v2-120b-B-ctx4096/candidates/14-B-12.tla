---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

(* MaxNat is a natural number, i.e., an element of Nat = 0.. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
====