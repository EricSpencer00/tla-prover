---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Finite version of the natural numbers, used to override Nat in the
   Boulanger specification during model checking. *)
NatOverride == 0 .. MaxNat

(* Instantiate the original Boulanger specification, supplying the
   constants required for model checking. *)
INSTANCE Boulanger AS B WITH
    N         <- N,
    max       <- MaxNat,
    Nat       <- NatOverride,
    num       <- [i \in 1..N |-> 0],
    previous  <- [i \in 1..N |-> 0],
    pc        <- [i \in 1..N |-> "idle"],
    unchecked <- {},
    nxt       <- [i \in 1..N |-> i],
    flag      <- [i \in 1..N |-> FALSE]

(* Export the specification and its key invariants under the names
   expected by the .cfg file. *)
Spec == B!Spec
MutualExclusion == B!MutualExclusion
TypeOK == B!TypeOK
Inv == B!Inv

(* State constraint: keep all ticket numbers strictly below MaxNat so that
   they remain within the finite range provided by NatOverride. *)
StateConstraint ==
    \A i \in 1..N : B!ticket[i] \in 0 .. (MaxNat - 1)

====