---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

MaxTicket == MaxNat - 1

VARIABLES inbox, status, ticket, count

vars == <<inbox, status, ticket, count>>

Init ==
  /\ inbox = [p \in 1..N |-> "none"]
  /\ status = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ count = 0

SendRequest(p) ==
  /\ status[p] = "idle"
  /\ inbox' = [inbox EXCEPT ![p] = "request"]
  /\ UNCHANGED <<status, ticket, count>>

TakeTicket(p) ==
  /\ status[p] = "idle"
  /\ inbox[p] = "request"
  /\ status' = [status EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = IF count < MaxTicket THEN count ELSE 0]
  /\ count' = IF count < MaxTicket THEN count + 1 ELSE 0
  /\ UNCHANGED inbox

EnterCS(p) ==
  /\ status[p] = "waiting"
  /\ \A q \in 1..N : (status[q] # "critical") \/ (ticket[q] > ticket[p])
  /\ status' = [status EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<inbox, ticket, count>>

ExitCS(p) ==
  /\ status[p] = "critical"
  /\ status' = [status EXCEPT ![p] = "idle"]
  /\ inbox' = [inbox EXCEPT ![p] = "none"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED count

Next ==
  \/ \E p \in 1..N : SendRequest(p)
  \/ \E p \in 1..N : TakeTicket(p)
  \/ \E p \in 1..N : EnterCS(p)
  \/ \E p \in 1..N : ExitCS(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : status[p] = "critical" => (\A q \in 1..N : (q # p) => status[q] # "critical")

TypeOK ==
  /\ inbox \in [1..N -> {"none", "request"}]
  /\ status \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> 0..MaxTicket]
  /\ count \in 0..MaxNat

Inv == TypeOK /\ MutualExclusion

NatOverride == Nat

====