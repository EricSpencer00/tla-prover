---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Definitions required by the Boulanger module *)
num       == N
previous  == 0
max       == MaxNat
pc        == [i \in 1..N |-> 0]          \* placeholder value
flag      == [i \in 1..N |-> FALSE]    \* placeholder value
unchecked == {}
nxt       == {}

(* Bring in the full Boulanger specification as an instance *)
INSTANCE Boulanger

(* State constraint: keep all tickets strictly below MaxNat *)
StateConstraint == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

(* Specification with the state constraint applied to Init and Next *)
Spec == Boulanger!Spec /\ StateConstraint /\ [][Boulanger!Next /\ StateConstraint]_{Boulanger!vars}

(* Export the invariants defined in Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====