---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0..MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

(* Original specification from the Boulanger module *)
OrigSpec == Boulanger!Spec

(* Specification used by the model checker, with the additional bound *)
Spec == OrigSpec /\ TicketBound

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====