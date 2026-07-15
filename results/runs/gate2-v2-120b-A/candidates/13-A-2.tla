---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket

(* ----------------------------------------------------------------------
   State definitions
   ---------------------------------------------------------------------- *)

(* pc[p] is the program counter of process p.
   It ranges over the symbolic names used in the original Bakery spec. *)
PCVals == {"idle", "trying", "waiting", "cs"}

(* ticket[p] is the ticket number of process p, or 0 if it has no ticket. *)
TicketVals == 0..MaxNat

(* ----------------------------------------------------------------------
   Init
   ---------------------------------------------------------------------- *)

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]

(* ----------------------------------------------------------------------
   Helper definitions (mirroring the original Bakery algorithm)
   ---------------------------------------------------------------------- *)

OtherTickets(p) == { ticket[q] : q \in 1..N, q # p }

(* The set of processes currently in the critical section *)
InCS == { p \in 1..N : pc[p] = "cs" }

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

Attempt(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = 1 + Max({ ticket[q] : q \in 1..N })]

PickNumber(p) ==
  /\ pc[p] = "trying"
  /\ \A q \in 1..N :
        (ticket[p] = 0) \/ (ticket[p] < ticket[q]) \/
        (ticket[p] = ticket[q] /\ p < q)
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED ticket

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]

(* The overall next-state relation *)
Next ==
  \E p \in 1..N : (Attempt(p) \/ PickNumber(p) \/ Exit(p))

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

ISpec == Init /\ [][Next]_<<pc, ticket>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

MutualExclusion == \A p, q \in 1..N : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
  /\ pc \in [1..N -> PCVals]
  /\ ticket \in [1..N -> TicketVals]

Inv ==
  /\ MutualExclusion
  /\ TypeOK

=============================================================================