---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(*--- Finite version of the natural numbers ---*)
NatOverride == 0 .. MaxNat

(*--- State constraint: ticket numbers must stay below MaxNat ---*)
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

(*--- Specification (initial condition and next-state relation) ---*)
Spec == Init /\ [][Next]_vars

(*--- Inherited invariants ---*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====