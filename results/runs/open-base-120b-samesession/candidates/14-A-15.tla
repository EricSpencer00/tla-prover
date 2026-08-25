---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANT N, MaxNat

(* Finite replacement for Nat *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay below MaxNat *)
TicketsBound == \A i \in 1..N : ticket[i] < MaxNat

(* Initialization and next-state relation inherited from Boulanger,
   augmented with the state constraint. *)
Init == Boulanger!Init /\ TicketsBound

Next == Boulanger!Next /\ TicketsBound'

(* Specification formula *)
Spec == Init /\ [][Next]_(Boulanger!vars)

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====