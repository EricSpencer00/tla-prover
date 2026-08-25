---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANT N, MaxNat

(* Finite version of the natural numbers for model checking. *)
NatOverride == 0 .. MaxNat

(* State constraint used in the .cfg file to keep tickets below MaxNat. *)
TicketConstraint ==
    \A i \in 1..N : ticket[i] < MaxNat

(* Specification of the system. *)
Spec == Init /\ [][Next]_vars /\ TicketConstraint

(* Invariants inherited from the Boulanger specification. *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====