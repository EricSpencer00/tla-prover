---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, served

vars == <<inCS, ticket, nextTicket, served>>

\* The bakery algorithm's ticket numbers are bounded by MaxNat for model checking.
NatOverride == 0..MaxNat

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN}
  /\ ticket \in [1..N -> NatOverride}
  /\ nextTicket \in NatOverride
  /\ served \in 0..MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ served = 0

\* A process takes a ticket and enters the critical section only when its ticket
\* is strictly lower than every other process's ticket (or that process is not in CS).
Enter(i) ==
  /\ ~inCS[i]
  /\ ticket[i] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED served

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED nextTicket

Next == \E i \in 1..N : Enter(i) \/ Exit(i)

ISpec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : inCS[i] => ticket[i] > 0
  /\ \A i, j \in 1..N :
       (inCS[i] /\ inCS[j] /\ i # j) => ticket[i] # ticket[j]

====