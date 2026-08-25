---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Instance of Boulanger with overridden Nat *)
INSTANCE Boulanger AS B WITH Nat <- NatOverride

(* Exported definitions from the instance *)
Init == B!Init
Next == B!Next
vars == B!vars
ticket == B!ticket

MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

(* Full specification used by the .cfg file *)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

====