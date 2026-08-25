---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of the natural numbers used for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers must stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification: initial condition, next‑state relation, and the state constraint *)
Spec == Init /\ [][Next]_vars /\ StateConstraint

(* Invariants required by the configuration file *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====