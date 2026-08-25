---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(*--------------------------------------------------------------------
  Finite version of Nat for model checking.
  The .cfg file will replace Nat with NatOverride.
--------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*--------------------------------------------------------------------
  Aliases to the definitions from the Boulanger specification.
--------------------------------------------------------------------*)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(*--------------------------------------------------------------------
  State constraint: all ticket numbers must stay strictly below MaxNat.
  It is assumed that the Boulanger specification defines a function
  `ticket` mapping each process (1..N) to a natural number.
--------------------------------------------------------------------*)
StateConstraint == 
    \A i \in 1 .. N : ticket[i] < MaxNat

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