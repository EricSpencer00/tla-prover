---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N
CONSTANT MaxNat

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

(* Specification of the system *)
Spec == Boulanger!Spec

(* Safety invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====