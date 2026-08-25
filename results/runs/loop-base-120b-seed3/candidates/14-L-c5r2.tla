---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Include the Boulanger algorithm specification as a named instance,
   providing concrete values for all of its parameters. *)
INSTANCE Boulanger AS B WITH
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
StateConstraint == \A i \in 1..N : B!ticket[i] < MaxNat

(* Specification and properties, with the state constraint added to the spec. *)
Spec == B!Spec /\ []StateConstraint
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv
====