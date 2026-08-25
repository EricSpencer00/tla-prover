---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: keep all tickets strictly below MaxNat *)
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

(* Specification with the state constraint applied to Init and Next *)
Spec == Init /\ StateConstraint /\ [][Next /\ StateConstraint]_vars

(* Export the invariants defined in Boulanger *)
MutualExclusion == Boulanger.MutualExclusion
TypeOK          == Boulanger.TypeOK
Inv             == Boulanger.Inv

====