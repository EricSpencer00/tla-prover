---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES holder, param, phase, want, ticket

vars == <<holder, param, phase, want, ticket>>

Phases == {"idle", "armed", "holding"}

Init ==
    /\ holder = [x \in 1..N |-> 0]
    /\ param = 0
    /\ phase = [x \in 1..N |-> "idle"]
    /\ want = [x \in 1..N |-> FALSE]
    /\ ticket = [x \in 1..N |-> 0]

BeginAquire(x) ==
    /\ phase[x] = "idle"
    /\ phase' = [phase EXCEPT ![x] = "armed"]
    /\ want' = [want EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<holder, param, ticket>>

TryEnter(x) ==
    /\ phase[x] = "armed"
    /\ \A y \in 1..N : holder[y] = 0
    /\ holder' = [holder EXCEPT ![x] = param]
    /\ phase' = [phase EXCEPT ![x] = "holding"]
    /\ ticket' = [ticket EXCEPT ![x] = IF ticket[x] < MaxNat THEN ticket[x] + 1 ELSE ticket[x]]
    /\ UNCHANGED <<param, want>>

Release(x) ==
    /\ phase[x] = "holding"
    /\ holder' = [holder EXCEPT ![x] = 0]
    /\ phase' = [phase EXCEPT ![x] = "idle"]
    /\ want' = [want EXCEPT ![x] = FALSE]
    /\ UNCHANGED <<param, ticket>>

Reconfig ==
    /\ param' = (param % N) + 1
    /\ UNCHANGED <<holder, phase, want, ticket>>

Next ==
    \/ \E x \in 1..N : BeginAquire(x)
    \/ \E x \in 1..N : TryEnter(x)
    \/ \E x \in 1..N : Release(x)
    \/ Reconfig

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ holder \in [1..N -> 0..N]
    /\ param \in 1..N
    /\ phase \in [1..N -> Phases]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]

MutualExclusion ==
    \A x \in 1..N : (holder[x] # 0) => (holder[x] = param)

Inv ==
    /\ MutualExclusion
    /\ TypeOK

TicketBound == \A x \in 1..N : ticket[x] <= MaxNat

====