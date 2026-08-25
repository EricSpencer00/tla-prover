---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(* State constraint: all ticket numbers must stay strictly below MaxNat *)
StateConstraint == \A i \in Proc : ticket[i] < MaxNat

(* Full specification, inheriting Init, Next and the variable set from Boulanger,
   and enforcing the state constraint at every step. *)
Spec == Init /\ [][Next]_vars /\ []StateConstraint

====