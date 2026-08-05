---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, waiting

vars == <<inCS, ticket, nextTicket, waiting>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ waiting \in [1..N -> BOOLEAN]

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ waiting = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ ~waiting[i]
  /\ ~inCS[i]
  /\ nextTicket < MaxNat
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED inCS

Enter(i) ==
  /\ waiting[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket, waiting>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : inCS[i] => \A j \in 1..N : (waiting[j] /\ ticket[j] < ticket[i]) => FALSE

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====