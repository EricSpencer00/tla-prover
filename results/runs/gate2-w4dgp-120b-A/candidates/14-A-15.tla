---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES lock, pc, served, tickets

TypeState ==
  /\ lock \in 0..N
  /\ pc \in [1..N -> {"idle", "trying", "critical"}]
  /\ served \in 0..MaxNat
  /\ tickets \in [1..N -> 0..MaxNat]

Init ==
  /\ lock = 0
  /\ pc = [i \in 1..N |-> "idle"]
  /\ served = 0
  /\ tickets = [i \in 1..N |-> 0]

Ticket(i) ==
  /\ pc[i] = "idle"
  /\ lock = 0
  /\ tickets[i] < MaxNat
  /\ lock' = i
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]
  /\ UNCHANGED served

Enter(i) ==
  /\ pc[i] = "trying"
  /\ lock = i
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<lock, tickets, served>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ lock = i
  /\ served < MaxNat
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ lock' = 0
  /\ served' = served + 1
  /\ UNCHANGED tickets

Next == \E i \in 1..N : Ticket(i) \/ Enter(i) \/ Exit(i)

Spec == Init /\ [][Next]_<<lock, pc, served, tickets>>

MutualExclusion == \A i \in 1..N : pc[i] = "critical" => lock = i

Inv == TypeState

NatOverride == \E n \in 0..MaxNat : TRUE

====