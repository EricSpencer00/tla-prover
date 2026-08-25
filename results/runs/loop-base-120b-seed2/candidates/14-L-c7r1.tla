---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N
CONSTANT MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Instantiate the original Boulanger specification, mapping the constant N *)
INSTANCE Boulanger AS B WITH N <- N

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1 .. N : B!ticket[i] < MaxNat

(* Export the main specification and invariants from the instantiated module *)
Spec == B!Spec
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====