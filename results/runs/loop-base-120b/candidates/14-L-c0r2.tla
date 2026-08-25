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
INSTANCE Boulanger AS B WITH N <- N

(*--------------------------------------------------------------------
  Aliases to the definitions from the instantiated Boulanger module.
--------------------------------------------------------------------*)
Init == B!Init
Next == B!Next
vars == B!vars

(*--------------------------------------------------------------------
  State constraint: all ticket numbers must stay strictly below MaxNat.
--------------------------------------------------------------------*)
StateConstraint ==
    \A i \in 1 .. N : B!ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Specification of the system, including the state constraint.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

(*--------------------------------------------------------------------
  Invariants inherited from the Boulanger specification.
--------------------------------------------------------------------*)
MutualExclusion == B!MutualExclusion
TypeOK           == B!TypeOK
Inv              == B!Inv

====