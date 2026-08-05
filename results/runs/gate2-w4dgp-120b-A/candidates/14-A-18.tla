---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES state, ticket, served, requesting

vars == <<state, ticket, served, requesting>>

NAT == 0..MaxNat

TypeOK ==
  /\ state \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> NAT]
  /\ served \in [1..N -> NAT]
  /\ requesting \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A i \in 1..N : state[i] = "critical" => (\A j \in 1..N : j # i => state[j] # "critical")

Init ==
  /\ state = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ served = [i \in 1..N |-> 0]
  /\ requesting = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ state[i] = "idle"
  /\ ~requesting[i]
  /\ requesting' = [requesting EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<state, ticket, served>>

Dequeue(i) ==
  /\ requesting[i]
  /\ requesting' = [requesting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<state, ticket, served>>

Reset(i) ==
  /\ state[i] = "critical"
  /\ state' = [state EXCEPT ![i] = "idle"]
  /\ served' = [served EXCEPT ![i] = @ + 1]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED requesting

Next ==
  \/ \E i \in 1..N : Request(i) \/ Dequeue(i) \/ Reset(i)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : state[i] = "idle" => \A j \in 1..N : j < i => ticket[j] < ticket[i]

TicketBound == \A i \in 1..N : ticket[i] < MaxNat
====