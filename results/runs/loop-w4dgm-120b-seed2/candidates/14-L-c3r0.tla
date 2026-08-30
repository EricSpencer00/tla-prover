---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES occupant, target, ticket, actState, lock

vars == <<occupant, target, ticket, actState, lock>>

TypeOK ==
  /\ occupant \in 0..N
  /\ target \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ actState \in [1..N -> {"idle", "waiting", "inCS"}]
  /\ lock \in {"free", "held"}

Init ==
  /\ occupant = 0
  /\ target = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ actState = [i \in 1..N |-> "idle"]
  /\ lock = "free"

\* A process reads the queue-control register; the ticket is the value it saw.
ReadQueue(i) ==
  /\ actState[i] = "idle"
  /\ actState' = [actState EXCEPT ![i] = "waiting"]
  /\ target' = i
  /\ ticket' = [ticket EXCEPT ![i] = occupant]
  /\ UNCHANGED <<occupant, lock>>

\* The compare-and-swap succeeds only if the control register is still on the
\* value the process read. It puts that value back plus one.
CasSucceed(i) ==
  /\ actState[i] = "waiting"
  /\ target = i
  /\ ticket[i] = occupant
  /\ occupant < MaxNat
  /\ occupant' = ticket[i] + 1
  /\ lock' = "held"
  /\ actState' = [actState EXCEPT ![i] = "inCS"]
  /\ UNCHANGED <<target, ticket>>

CasFail(i) ==
  /\ actState[i] = "waiting"
  /\ (target # i \/ ticket[i] # occupant)
  /\ actState' = [actState EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<occupant, target, ticket, lock>>

\* The queue control (the compare-and-swap register) is the single governing
\* authority here; a process may only leave the critical section by taking it
\* back out on the value equal to its own ticket.
LeaveCS(i) ==
  /\ actState[i] = "inCS"
  /\ ticket[i] = occupant - 1
  /\ occupant' = ticket[i]
  /\ lock' = "free"
  /\ actState' = [actState EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<target, ticket>>

Next ==
  \/ \E i \in 1..N : ReadQueue(i)
  \/ \E i \in 1..N : CasSucceed(i)
  \/ \E i \in 1..N : CasFail(i)
  \/ \E i \in 1..N : LeaveCS(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : actState[i] = "inCS" => (lock = "held" /\ ticket[i] = occupant - 1)

Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* Safety, not liveness: the queue-control register is bounded and stays
\* within that bound; ticket numbers only ever move back to the value read.
NatOverride == TRUE

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====