---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES status, pc, ticket, nextTicket

vars == <<status, pc, ticket, nextTicket>>

Modes == {"idle", "trying", "critical"}

TypeOK ==
    /\ status \in [1..N -> {"idle", "trying", "critical"}]
    /\ pc \in 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ status = [i \in 1..N |-> "idle"]
    /\ pc = 1
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

Acquire ==
    /\ status[pc] = "idle"
    /\ status' = [status EXCEPT ![pc] = "trying"]
    /\ UNCHANGED <<pc, ticket, nextTicket>>

Enter ==
    /\ status[pc] = "trying"
    /\ \A j \in 1..N : status[j] # "critical"
    /\ status' = [status EXCEPT ![pc] = "critical"]
    /\ ticket' = [ticket EXCEPT ![pc] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED pc

Exit ==
    /\ status[pc] = "critical"
    /\ status' = [status EXCEPT ![pc] = "idle"]
    /\ UNCHANGED <<pc, ticket, nextTicket>>

Pass ==
    /\ pc' = (pc % N) + 1
    /\ UNCHANGED <<status, ticket, nextTicket>>

Next ==
    \/ Acquire
    \/ Enter
    \/ Exit
    \/ Pass

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (status[i] = "critical" /\ status[j] = "critical") => i = j

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in 1..N : status[i] = "critical" => ticket[i] = nextTicket - 1

TicketBound == \A i \in 1..N : ticket[i] <= MaxNat

====