---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of the natural numbers set *)
NatOverride == 0 .. MaxNat

(* Inherit the core definitions from the Boulanger specification *)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(* State constraint: ticket numbers must stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Overall specification with the state constraint applied *)
Spec == Init /\ [][Next /\ StateConstraint]_vars

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====