---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*--------------------------------------------------------------------
  Finite version of the natural numbers used for model checking.
--------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*--------------------------------------------------------------------
  State constraint: all ticket numbers must stay strictly below MaxNat.
--------------------------------------------------------------------*)
NoOverflow == \A i \in 1..N : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Initialization and next-state relation, inheriting from Boulanger
  and adding the overflow constraint.
--------------------------------------------------------------------*)
Init == Boulanger!Init /\ NoOverflow
Next == Boulanger!Next

(*--------------------------------------------------------------------
  Specification formula required by the .cfg file.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants required by the .cfg file.
--------------------------------------------------------------------*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====