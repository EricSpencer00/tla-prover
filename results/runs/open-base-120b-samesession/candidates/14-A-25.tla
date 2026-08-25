---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite replacement for the infinite set Nat *)
NatOverride == 0..MaxNat

(* State constraint: keep all ticket numbers strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification for model checking *)
Spec == Init /\ [][Next]_vars /\ StateConstraint

(* Invariants inherited from the Boulanger specification *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====