---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES token, upstairs, waiting, myTicket

vars == <<token, upstairs, waiting, myTicket>>

Bump(n) == IF n < MaxNat THEN n + 1 ELSE n

TypeOK ==
  /\ token \in 0..MaxNat
  /\ upstairs \in 0..N
  /\ waiting \in 0..N
  /\ myTicket \in [0..(N-1) -> 0..MaxNat]

Init ==
  /\ token = 0
  /\ upstairs = 0
  /\ waiting = 0
  /\ myTicket = [p \in 0..(N-1) |-> 0]

Request(p) ==
  /\ myTicket[p] = 0
  /\ myTicket' = [myTicket EXCEPT ![p] = Bump(token)]
  /\ waiting' = (waiting + 1) % (N + 1)
  /\ UNCHANGED <<token, upstairs>>

GoUp(p) ==
  /\ myTicket[p] > 0
  /\ myTicket[p] = token
  /\ upstairs = 0
  /\ upstairs' = p + 1
  /\ UNCHANGED <<token, waiting, myTicket>>

GoDown(p) ==
  /\ upstairs = p + 1
  /\ upstairs' = 0
  /\ myTicket' = [myTicket EXCEPT ![p] = 0]
  /\ UNCHANGED <<token, waiting>>

PassToken ==
  /\ upstairs = 0
  /\ token < MaxNat
  /\ token' = token + 1
  /\ UNCHANGED <<upstairs, waiting, myTicket>>

Next ==
  \/ \E p \in 0..(N-1) : Request(p)
  \/ \E p \in 0..(N-1) : GoUp(p)
  \/ \E p \in 0..(N-1) : GoDown(p)
  \/ PassToken

Spec == Init /\ [][Next]_vars

MutualExclusion == upstairs >= 1 => myTicket[upstairs - 1] = token

Inv == TypeOK /\ MutualExclusion

TicketBound == \A p \in 0..(N-1) : myTicket[p] < MaxNat

====