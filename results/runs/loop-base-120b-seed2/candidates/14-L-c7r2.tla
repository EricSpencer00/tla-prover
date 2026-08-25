---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N
CONSTANT MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Instantiate the original Boulanger specification, mapping the constant N *)
INSTANCE Boulanger WITH N <- N

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1 .. N : Boulanger!ticket[i] < MaxNat

(* Export the main specification and invariants from the instantiated module *)
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====