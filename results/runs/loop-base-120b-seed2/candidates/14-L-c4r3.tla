---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC, Boulanger

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Aliases for invariants defined in the Boulanger module *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

(* Full specification used by the .cfg file *)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

====