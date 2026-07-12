---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANTS N, MaxNat, Nat

(* Ensure that the configured Nat set is the finite range 0..MaxNat *)
ASSUME Nat = 0 .. MaxNat

(* State constraint that keeps each process’s ticket number strictly below MaxNat *)
StateConstraint == \A i \in 1..N: Ticket[i] < MaxNat

(* Full behavioral specification with the added state constraint *)
Spec == Init /\ [][Next]_vars /\ StateConstraint

(* Inherit invariants from the Boulanger specification *)
MutualExclusion == BoulangerMutualExclusion
TypeOK          == BoulangerTypeOK
Inv             == BoulangerInv

====