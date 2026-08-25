---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

(***************************************************************************)
(*  Definitions required by the parameterised Boulanger specification      *)
(***************************************************************************)

(* Number of processes *)
num == N

(* Upper bound for ticket numbers *)
max == MaxNat

(* Auxiliary constants used by the Boulanger algorithm – concrete values
   are not important for the model‑checking configuration, they only need
   to exist and have the correct type. *)
previous == 0
unchecked == {}          \* a set of processes
nxt       == 0
flag      == FALSE      \* a Boolean flag (used as a constant placeholder)

(***************************************************************************)
(*  Instantiate the full Boulanger specification                              *)
(***************************************************************************)
INSTANCE Boulanger

(***************************************************************************)
(*  State constraint: keep all ticket numbers strictly below MaxNat.       *)
(***************************************************************************)
StateConstraint ==
    \A i \in 1..N : Boulanger!tickets[i] < MaxNat

(***************************************************************************)
(*  Specification used by the model checker                                 *)
(***************************************************************************)
Spec == Boulanger!Spec /\ StateConstraint

(***************************************************************************)
(*  Inherited safety properties                                            *)
(***************************************************************************)
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv
====