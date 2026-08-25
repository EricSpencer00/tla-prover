---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Bring in the full Boulanger specification *)
INSTANCE Boulanger

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == 
    \A i \in 1..N : Boulanger!tickets[i] < MaxNat

(* Specification used by the model checker *)
Spec == Boulanger!Spec /\ StateConstraint

(* Inherited safety properties *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====