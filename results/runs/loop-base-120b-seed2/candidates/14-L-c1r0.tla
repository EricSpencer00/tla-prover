---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* Bring in the full Boulanger specification *)
INSTANCE Boulanger AS B

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == 
    \A i \in 1..N : B.tickets[i] < MaxNat

(* Specification used by the model checker *)
Spec == B.Spec /\ StateConstraint

(* Inherited safety properties *)
MutualExclusion == B.MutualExclusion
TypeOK          == B.TypeOK
Inv             == B.Inv
====