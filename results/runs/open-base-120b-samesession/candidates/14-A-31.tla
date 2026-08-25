---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------
  Finite override for the infinite set Nat.
  NatOverride is used (via the .cfg) to replace Nat in the
  inherited specification.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------
  State constraint: all ticket numbers must stay strictly below MaxNat.
  The .cfg can refer to this operator as a STATE CONSTRAINT.
-----------------------------------------------------------------*)
StateConstraint == 
  \A p \in 1..N : ticket[p] < MaxNat

(*-----------------------------------------------------------------
  Specification: inherits Init and Next from Boulanger.
-----------------------------------------------------------------*)
Init == Boulanger!Init
Next == Boulanger!Next

Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariants inherited from Boulanger.
-----------------------------------------------------------------*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====