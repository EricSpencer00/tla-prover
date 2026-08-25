---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(*--------------------------------------------------------------------
  Finite version of Nat for model checking.
  The .cfg file will replace Nat with NatOverride.
--------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*--------------------------------------------------------------------
  Instantiate the Boulanger algorithm, wiring the constant N.
--------------------------------------------------------------------*)
INSTANCE Boulanger WITH N <- N

(*--------------------------------------------------------------------
  Aliases to the definitions from the instantiated Boulanger module.
--------------------------------------------------------------------*)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(*--------------------------------------------------------------------
  State constraint: all ticket numbers must stay strictly below MaxNat.
--------------------------------------------------------------------*)
StateConstraint ==
    \A i \in 1 .. N : Boulanger!ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Specification of the system, including the state constraint.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

(*--------------------------------------------------------------------
  Invariants inherited from the Boulanger specification.
--------------------------------------------------------------------*)
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====