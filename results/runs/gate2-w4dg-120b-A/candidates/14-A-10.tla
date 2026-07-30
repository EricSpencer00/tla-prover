---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME N \in Nat /\ N >= 2 /\ MaxNat \in Nat /\ MaxNat >= 1

VARIABLES pc, requesting, served, ticket, clock

vars == <<pc, requesting, served, ticket, clock>>

States == {"idle", "trying", "critical", "done"}

TypeOK ==
  /\ pc \in [1..N -> States]
  /\ requesting \in 0..N
  /\ served \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ clock \in 0..MaxNat

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ requesting = 0
  /\ served = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ clock = 0

Begin(i) ==
  /\ pc[i] = "idle"
  /\ requesting < N
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ requesting' = requesting + 1
  /\ UNCHANGED <<served, ticket, clock>>

Tick ==
  /\ pc' = pc
  /\ requesting' = requesting
  /\ served' = served
  /\ ticket' = ticket
  /\ clock' = (clock + 1) % (MaxNat + 1)

Enter(i) ==
  /\ pc[i] = "trying"
  /\ ticket[i] = 0
  /\ \A j \in 1..N : (pc[j] # "critical") => (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i))
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<requesting, served, ticket, clock>>

Assign(i) ==
  /\ pc[i] = "trying"
  /\ ticket[i] = 0
  /\ \A j \in 1..N : (pc[j] # "critical") => ticket[j] < clock
  /\ ticket' = [ticket EXCEPT ![i] = clock]
  /\ UNCHANGED <<pc, requesting, served, clock>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ served < N
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ served' = served + 1
  /\ UNCHANGED <<requesting, ticket, clock>>

Next ==
  \/ \E i \in 1..N : Begin(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Assign(i)
  \/ \E i \in 1..N : Exit(i)
  \/ Tick

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : (pc[i] = "critical") => (\A j \in 1..N : j # i => pc[j] # "critical")

Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : (pc[i] = "critical") => (served > 0)
  /\ \A i \in 1..N : (pc[i] = "critical") => (served >= ticket[i])

TicketBound ==
  \A i \in 1..N : ticket[i] < MaxNat

====