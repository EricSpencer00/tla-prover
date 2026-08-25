---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* ----------------------------------------------------------------------
   Finite version of the natural numbers used for model checking.
   The configuration file replaces the standard Nat with this operator.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   Specification – reuse the full behavioral specification from Boulanger.
   ---------------------------------------------------------------------- *)
Spec == Boulanger!Spec

(* ----------------------------------------------------------------------
   Invariants – inherit the invariants defined in the Boulanger module.
   ---------------------------------------------------------------------- *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

(* ----------------------------------------------------------------------
   State constraint – ensure that all ticket numbers stay strictly below
   the maximum value, keeping the finite NatOverride consistent.
   ---------------------------------------------------------------------- *)
StateConstraint == 
    \A i \in 1 .. N : ticket[i] < MaxNat

====