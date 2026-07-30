---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, nextTicket, served

vars == <<pc, ticket, nextTicket, served>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ served \in 0..MaxNat

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ served = 0

Request(i) ==
  /\ pc[i] = "idle"
  /\ nextTicket < MaxNat
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED served

Enter(i) ==
  /\ pc[i] = "trying"
  /\ \A j \in 1..N : (pc[j] = "critical") => (ticket[i] < ticket[j])
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, nextTicket, served>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : pc[i] = "critical" => \A j \in 1..N : (pc[j] = "critical") => ticket[i] <= ticket[j]

====