---- MODULE MCBoulanger ----
EXTENDS Boulanger, Naturals

CONSTANTS N, MaxNat

(* Finite override of the natural numbers set. *)
NatOverride == 0 .. MaxNat

(* Re‑export of the base specification's components. *)
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

(* State constraint: every process's ticket number stays strictly below MaxNat. *)
TicketBound == /\ \A i \in 1..N: ticket[i] < MaxNat

(* Whole specification for model checking. *)
Spec == Init /\ [][Next]_vars /\ TicketBound

(* Invariants required by the .cfg file. *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv

====