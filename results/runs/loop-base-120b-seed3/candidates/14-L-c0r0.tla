---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers stay strictly below the maximum *)
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

(* Specification: inherits Boulanger's spec and applies the state constraint *)
Spec == Boulanger.Spec /\ []TicketBound

(* Safety invariants, directly re‑using those defined in Boulanger *)
MutualExclusion == Boulanger.MutualExclusion
TypeOK           == Boulanger.TypeOK
Inv              == Boulanger.Inv
====