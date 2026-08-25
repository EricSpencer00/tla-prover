---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite version of the natural numbers, used via the .cfg replacement *)
NatOverride == 0 .. MaxNat

(* State constraint: ticket numbers must stay strictly below MaxNat *)
StateConstraint == 
    \A i \in Proc : ticket[i] < MaxNat

(* Full specification for model checking *)
Spec == Init /\ [][Next]_vars /\ StateConstraint

====