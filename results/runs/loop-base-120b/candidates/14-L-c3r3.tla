---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0..MaxNat

(* Definitions required by the Boulanger algorithm *)
num == NatOverride
previous == NatOverride
max == MaxNat
pc == NatOverride
unchecked == NatOverride
nxt == NatOverride
flag == BOOLEAN

(* Instantiate the Boulanger algorithm, providing the required symbols *)
INSTANCE Boulanger WITH
    N <- N,
    num <- num,
    previous <- previous,
    max <- max,
    pc <- pc,
    unchecked <- unchecked,
    nxt <- nxt,
    flag <- flag

(* State constraint: all ticket numbers stay strictly below MaxNat *)
TicketBound == \A i \in 1..N : Boulanger!Ticket[i] < MaxNat

(* Specification used by the model checker, with the additional bound *)
Spec == Boulanger!Spec /\ TicketBound

(* Invariants inherited from Boulanger *)
MutualExclusion == Boulanger!MutualExclusion
TypeOK == Boulanger!TypeOK
Inv == Boulanger!Inv
====