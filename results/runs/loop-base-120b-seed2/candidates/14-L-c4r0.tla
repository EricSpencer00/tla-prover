---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Import the full Boulanger specification, overriding Nat with NatOverride *)
INSTANCE Boulanger WITH Nat <- NatOverride

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == 
    \A i \in 1..N : ticket[i] < MaxNat

(* Full specification used by the .cfg file *)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

====