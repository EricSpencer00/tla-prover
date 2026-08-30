---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES holder, inCS, ticket, served

vars == <<holder, inCS, ticket, served>>

Bump(n) == IF n < MaxNat THEN n + 1 ELSE 0

TypeOK ==
  /\ holder \in 0..N
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ served \subseteq 1..N

Init ==
  /\ holder = 0
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ served = {}

Request(i) ==
  /\ ~inCS[i]
  /\ holder # i
  /\ holder' = i
  /\ ticket' = [ticket EXCEPT ![i] = Bump(@)]
  /\ UNCHANGED <<inCS, served>>

Enter(i) ==
  /\ holder = i
  /\ ~inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<holder, ticket, served>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ served' = served \cup {i}
  /\ holder' = 0
  /\ UNCHANGED ticket

Idle ==
  /\ served = 1..N
  /\ UNCHANGED vars

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ Idle

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : inCS[i] => holder = i

Inv ==
  \A i \in 1..N : inCS[i] => (holder = i /\ ticket[i] = MaxNat)

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====