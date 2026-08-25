---- MODULE MCBoulanger ----
EXTENDS Naturals
CONSTANTS MaxNat
INSTANCE Boulanger AS B

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay strictly below the maximum *)
TicketBound == \A i \in 1..N : B!ticket[i] < MaxNat

(* Specification: inherits Boulanger's spec and applies the state constraint *)
Spec == B!Spec /\ []TicketBound

(* Safety invariants, re‑exposed from Boulanger *)
MutualExclusion == B!MutualExclusion
TypeOK           == B!TypeOK
Inv              == B!Inv
====