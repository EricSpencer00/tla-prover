---- MODULE MCBakery ----
EXTENDS FiniteSets, Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, haveTicket, maxTicket

vars == <<inCS, ticket, haveTicket, maxTicket>>

RECURSIVE NatOverride(_)
NatOverride(S) == { IF x = MaxNat THEN MaxNat ELSE x : x \in S }

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ haveTicket \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ haveTicket = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxTicket = 0

Enter(i) ==
  /\ ~haveTicket[i]
  /\ haveTicket' = [haveTicket EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ UNCHANGED inCS

CS(i) ==
  /\ haveTicket[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, haveTicket, maxTicket>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ haveTicket' = [haveTicket EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, maxTicket>>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : CS(i)
  \/ \E i \in 1..N : Exit(i)

Inv ==
  /\ \A i, j \in 1..N : inCS[i] /\ inCS[j] => i = j
  /\ TypeOK

ISpec == Init /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : Exit(i))

====