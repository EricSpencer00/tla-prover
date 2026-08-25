---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: ticket numbers stay strictly below MaxNat *)
TicketBound == \A i \in 1..N: ticket[i] < MaxNat

(* Specification with the state constraint *)
Spec == Boulanger!Spec /\ []TicketBound

(* Expose the basic components of the underlying specification *)
Init == Boulanger!Init
Next == Boulanger!Next

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====