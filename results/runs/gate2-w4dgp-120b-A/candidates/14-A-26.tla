---- MODULE MCBoulanger ----
EXTENDS FiniteSets, Naturals

CONSTANTS N, MaxNat

VARIABLES value, ticket, maxTicket, status, lastWriter

vars == <<value, ticket, maxTicket, status, lastWriter>>

None == "none"
Idle == "idle"
Waiting == "waiting"
Writing == "writing"

bakers == 0..(N - 1)

TypeOK ==
  /\ value \in Nat
  /\ ticket \in [bakers -> Nat]
  /\ maxTicket \in Nat
  /\ status \in [bakers -> {Idle, Waiting, Writing}]
  /\ lastWriter \in (bakers \cup {None})

Init ==
  /\ value = 0
  /\ ticket = [b \in bakers |-> 0]
  /\ maxTicket = 0
  /\ status = [b \in bakers |-> Idle]
  /\ lastWriter = None

Read ==
  /\ \E b \in bakers :
       /\ status[b] = Idle
       /\ \A o \in bakers : status[o] # Waiting
       /\ maxTicket < MaxNat
       /\ ticket' = [ticket EXCEPT ![b] = maxTicket + 1]
       /\ maxTicket' = maxTicket + 1
       /\ status' = [status EXCEPT ![b] = Waiting]
  /\ UNCHANGED <<value, lastWriter>>

Acquire ==
  /\ \E b \in bakers :
       /\ status[b] = Waiting
       /\ \A o \in bakers : (status[o] = Writing) => ticket[o] > ticket[b]
       /\ status' = [status EXCEPT ![b] = Writing]
  /\ UNCHANGED <<value, ticket, maxTicket, lastWriter>>

Release ==
  /\ \E b \in bakers :
       /\ status[b] = Writing
       /\ value' = value + 1
       /\ lastWriter' = b
       /\ status' = [status EXCEPT ![b] = Idle]
  /\ UNCHANGED <<ticket, maxTicket>>

Next == Read \/ Acquire \/ Release

Spec == Init /\ [][Next]_vars

MutualExclusion == \A o \in bakers : status[o] = Writing => maxTicket = ticket[o]

Inv ==
  /\ (maxTicket > 0) => (maxTicket = ticket[lastWriter])
  /\ \A b \in bakers : (status[b] = Writing) => (maxTicket = ticket[b])

TicketBound == \A b \in bakers : ticket[b] < MaxNat

====