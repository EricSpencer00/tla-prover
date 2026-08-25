---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* ----------------------------------------------------------------------
   Finite version of the natural numbers set.
   The standard Nat set is overridden (via the .cfg) by NatOverride,
   which is limited to the range 0..MaxNat.
   ---------------------------------------------------------------------- *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   State constraint that all ticket numbers stay strictly below MaxNat.
   This operator can be referenced in the .cfg file as a STATE_CONSTRAINT.
   ---------------------------------------------------------------------- *)
StateConstraint ==
    \A i \in 1 .. N : Boulanger!ticket[i] < MaxNat

(* ----------------------------------------------------------------------
   Specification: the full behavior of the Boulanger algorithm, constrained
   by the state constraint above.
   ---------------------------------------------------------------------- *)
Spec == Boulanger!Spec /\ [] StateConstraint

(* ----------------------------------------------------------------------
   Invariants inherited from the Boulanger specification.
   ---------------------------------------------------------------------- *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

====