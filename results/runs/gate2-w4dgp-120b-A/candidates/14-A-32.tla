---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES ticket, maxTicket, inCS, waiting
vars == <<ticket, maxTicket, inCS, waiting>>

Nat == 0..MaxNat

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat
  /\ inCS \in [1..N -> BOOLEAN]
  /\ waiting \in [1..N -> BOOLEAN]

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ waiting = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ ~waiting[i]
  /\ ~inCS[i]
  /\ maxTicket < MaxNat
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED inCS

Enter(i) ==
  /\ waiting[i]
  /\ ~\E j \in 1..N : inCS[j]
  /\ \A j \in 1..N : waiting[j] => ticket[i] < ticket[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, maxTicket>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, maxTicket, waiting>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec ==
  /\ Init
  /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
  /\ (maxTicket > 0 => \E i \in 1..N : ticket[i] = maxTicket)
  /\ \A i \in 1..N : inCS[i] => (ticket[i] > 0 /\ ticket[i] <= maxTicket)
  /\ \A i \in 1..N : inCS[i] => \A j \in 1..N : waiting[j] => ticket[i] < ticket[j]

TicketRange == \A i \in 1..N : ticket[i] < MaxNat

====