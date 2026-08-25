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

(* Bring in the full Boulanger specification as a named instance *)
INSTANCE Boulanger AS B

(* Finite version of Nat for model checking *)
NatOverride == { n \in Nat : n <= MaxNat }

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint ==
    /\ \A i \in 1..N : B!ticket[i] < MaxNat

(* Re‑export the core components of the Boulanger specification *)
Init == B!Init
Next == B!Next
vars == B!vars

(* The specification to be checked by TLC *)
Spec == Init /\ StateConstraint /\ [][Next]_vars

(* Invariants inherited from Boulanger *)
MutualExclusion == B!MutualExclusion
TypeOK           == B!TypeOK
Inv              == B!Inv

====