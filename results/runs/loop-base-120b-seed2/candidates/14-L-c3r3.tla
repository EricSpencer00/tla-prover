---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, num, previous, max, pc, unchecked, nxt, flag

(* Parameter definitions required by the Boulanger module *)
num       == N
previous  == MaxNat
max       == MaxNat
pc        == N
unchecked == N
nxt       == N
flag      == N

(* Bring in the full Boulanger specification as an instance *)
INSTANCE Boulanger

(* Finite version of Nat for model checking *)
NatOverride == { n \in Nat : n <= MaxNat }

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint ==
    /\ \A i \in 1..N : Boulanger!ticket[i] < MaxNat

(* Re‑export the core components of the Boulanger specification *)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(* The specification to be checked by TLC *)
Spec == Init /\ StateConstraint /\ [][Next]_vars

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv
====