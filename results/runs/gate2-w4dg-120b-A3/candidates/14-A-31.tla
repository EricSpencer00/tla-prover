---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, num, nextTicket

vars == <<pc, num, nextTicket>>

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ num = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ UNCHANGED <<num, nextTicket>>

Enter(i) ==
  /\ pc[i] = "trying"
  /\ \A j \in 1..N : pc[j] # "critical" \/ num[i] < num[j]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<num, nextTicket>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<num, nextTicket>>

AssignTicket(i) ==
  /\ pc[i] = "trying"
  /\ nextTicket < MaxNat
  /\ num' = [num EXCEPT ![i] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED pc

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : AssignTicket(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "critical"}]
  /\ num \in [1..N -> Nat]
  /\ nextTicket \in Nat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

BoundTickets == \A i \in 1..N : num[i] < MaxNat

====