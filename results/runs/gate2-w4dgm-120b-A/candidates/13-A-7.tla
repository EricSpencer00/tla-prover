---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* NatOverride replaces Nat (redeclared as a finite range for model checking).
NatOverride == 0..MaxNat

VARIABLES inCS, wants, ticket, maxTicket

Vars == <<inCS, wants, ticket, maxTicket>>

\* Mutual exclusion: no two processes are ever in the critical section together.
MutualExclusion == \A i, j \in 0..(N-1) : (i /= j) => ~(inCS[i] /\ inCS[j])

TypeOK ==
  /\ inCS \in [0..(N-1) -> BOOLEAN]
  /\ wants \in [0..(N-1) -> BOOLEAN]
  /\ ticket \in [0..(N-1) -> NatOverride]
  /\ maxTicket \in NatOverride

Inv ==
  /\ MutualExclusion
  /\ TypeOK

Init ==
  /\ inCS = [i \in 0..(N-1) |-> FALSE]
  /\ wants = [i \in 0..(N-1) |-> FALSE]
  /\ ticket = [i \in 0..(N-1) |-> 0]
  /\ maxTicket = 0

Request(i) ==
  /\ ~wants[i]
  /\ ~inCS[i]
  /\ wants' = [wants EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket, maxTicket>>

IssueTicket(i) ==
  /\ wants[i]
  /\ ~inCS[i]
  /\ maxTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket + 1]
  /\ maxTicket' = maxTicket + 1
  /\ UNCHANGED <<inCS, wants>>

Enter(i) ==
  /\ wants[i]
  /\ ~inCS[i]
  /\ \A j \in 0..(N-1) : ~inCS[j]
  /\ \A j \in 0..(N-1) : (j = i) \/ (ticket[j] = 0) \/ (ticket[j] > ticket[i])
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<wants, ticket, maxTicket>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ wants' = [wants EXCEPT ![i] = FALSE]
  /\ UNCHANGED maxTicket

Next ==
  \/ \E i \in 0..(N-1) : Request(i) \/ IssueTicket(i) \/ Enter(i) \/ Exit(i)

ISpec == Init /\ [][Next]_Vars

====