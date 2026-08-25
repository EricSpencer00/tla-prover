---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Instantiate the Boulanger algorithm, passing the constant N *)
INSTANCE Boulanger WITH N <- N

(* Finite version of Nat for model checking *)
NatOverride == 0..MaxNat

(* State constraint: all ticket numbers stay strictly below MaxNat *)
TicketBound == \A i \in 1..N : Boulanger!Ticket[i] < MaxNat

(* Specification used by the model checker, with the additional bound *)
Spec == Boulanger!Spec /\ TicketBound

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====