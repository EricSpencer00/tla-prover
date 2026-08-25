---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Include the Boulanger algorithm specification as a named instance,
   providing concrete values for all of its parameters. *)
INSTANCE Boulanger WITH
    num        <- N,
    max        <- MaxNat,
    previous   <- 0,
    pc         <- [i \in 1..N |-> "idle"],
    unchecked  <- {},
    nxt        <- [i \in 1..N |-> 0],
    flag       <- [i \in 1..N |-> FALSE]

(* Finite version of the natural numbers used for model checking. *)
NatOverride == { i \in Nat : i <= MaxNat }

(* State constraint that keeps all ticket numbers strictly below MaxNat. *)
StateConstraint == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

Spec == Boulanger!Spec /\ []StateConstraint
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====