---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of the natural numbers, used to override Nat in the
   Boulanger specification during model checking. *)
NatOverride == 0 .. MaxNat

(* Export the specification and its key invariants under the names
   expected by the .cfg file. *)
Spec == Boulanger!Spec
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

(* State constraint: keep all ticket numbers strictly below MaxNat so that
   they remain within the finite range provided by NatOverride. *)
StateConstraint ==
    \A i \in 1..N : ticket[i] \in 0 .. (MaxNat - 1)

====