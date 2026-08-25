---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Initialization and step relation inherit from Boulanger, constrained by StateConstraint *)
Init == Boulanger!Init /\ StateConstraint
Next == Boulanger!Next /\ StateConstraint

(* Full specification *)
Spec == Init /\ [][Next]_vars

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====