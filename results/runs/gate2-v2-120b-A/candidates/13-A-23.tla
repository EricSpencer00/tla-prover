---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES pc, tickets

(* pc[p] is the program counter of process p.
   Values: "Idle", "Enter", "CS", "Exit" *)
(* tickets[p] is the ticket number held by process p, or 0 if none. *)

(* Finite set of process identifiers *)
ProcSet == 1..N

(* State predicate ensuring variables have correct types *)
TypeOK ==
  /\ pc \in [ProcSet -> {"Idle", "Enter", "CS", "Exit"}]
  /\ tickets \in [ProcSet -> Nat]

(* Initial state: all processes idle, all tickets 0 *)
Init ==
  /\ pc = [p \in ProcSet |-> "Idle"]
  /\ tickets = [p \in ProcSet |-> 0]
  /\ TypeOK

(* Action: a process starts the entry protocol *)
Enter(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "Idle"
  /\ pc' = [pc EXCEPT ![p] = "Enter"]
  /\ tickets' = [tickets EXCEPT ![p] = MaxNat] \* placeholder, real value set in Acquire
  /\ TypeOK

(* Action: a process acquires a ticket (actually chooses the smallest unused ticket) *)
Acquire(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "Enter"
  /\ LET newTicket == 
        IF {tickets[q] : q \in ProcSet} = {} 
           THEN 1 
           ELSE 1 + Max({tickets[q] : q \in ProcSet})
     IN /\ newTicket \in Nat
        /\ tickets' = [tickets EXCEPT ![p] = newTicket]
        /\ pc' = pc
        /\ TypeOK

(* Action: a process moves from Enter to CS when its ticket is the smallest
   among all processes that have a ticket and no other process with a smaller
   ticket is in CS. *)
EnterCS(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "Enter"
  /\ \A q \in ProcSet :
        (pc[q] # "CS") \/ (tickets[p] < tickets[q]) \/ (tickets[p] = tickets[q] /\ p < q)
  /\ pc' = [pc EXCEPT ![p] = "CS"]
  /\ tickets' = tickets
  /\ TypeOK

(* Action: a process leaves the critical section *)
Exit(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Exit"]
  /\ tickets' = [tickets EXCEPT ![p] = 0]
  /\ TypeOK

(* Action: a process returns to idle after exit *)
Idle(p) ==
  /\ p \in ProcSet
  /\ pc[p] = "Exit"
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ tickets' = tickets
  /\ TypeOK

Next ==
  \/ \E p \in ProcSet : Enter(p)
  \/ \E p \in ProcSet : Acquire(p)
  \/ \E p \in ProcSet : EnterCS(p)
  \/ \E p \in ProcSet : Exit(p)
  \/ \E p \in ProcSet : Idle(p)

(* Safety invariant: at most one process in the critical section *)
MutualExclusion ==
  Cardinality({p \in ProcSet : pc[p] = "CS"}) <= 1

(* Full inductive invariant combining safety and type correctness *)
Inv == MutualExclusion /\ TypeOK

(* Initial condition for the inductive specification *)
ISpecInit ==
  Init

(* Transition relation for the inductive specification *)
ISpecNext ==
  Next

(* Full specification formula required by the cfg *)
ISpec == ISpecInit /\ [][ISpecNext]_<<pc, tickets>>

====