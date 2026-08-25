---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(* Finite version of Nat, used by the .cfg to replace Nat *)
NatOverride == 0..MaxNat

(* Re‑export the core operators from Boulanger *)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(* State constraint: every ticket must stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification that incorporates the state constraint *)
Spec == Init /\ StateConstraint /\ [][Next /\ StateConstraint]_(vars)

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====