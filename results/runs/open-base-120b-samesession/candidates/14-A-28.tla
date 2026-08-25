---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

\* Finite replacement for the infinite set Nat
NatOverride == 0..MaxNat

\* Specification and invariants inherited from Boulanger
Spec == Boulanger!Spec

MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====