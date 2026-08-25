---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

(* Finite replacement for the infinite set Nat *)
NatOverride == 0 .. MaxNat

(* State constraint: ticket numbers must stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Specification for model checking *)
Spec == Init /\ [][Next /\ StateConstraint]_vars

====