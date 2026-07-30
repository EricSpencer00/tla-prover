---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES phase, ticket, clock
vars == <<phase, ticket, clock>>

TypeOK ==
    /\ phase \in [1..N -> {"idle", "trying", "inCS"}]
    /\ ticket \in [1..N -> 0..(MaxNat - 1)]
    /\ clock \in 0..(MaxNat - 1)

Init ==
    /\ phase = [i \in 1..N |-> "idle"]
    /\ ticket = [i \in 1..N |-> 0]
    /\ clock = 0

Begin(i) ==
    /\ phase[i] = "idle"
    /\ phase' = [phase EXCEPT ![i] = "trying"]
    /\ ticket' = [ticket EXCEPT ![i] = clock]
    /\ UNCHANGED clock

Enter(i) ==
    /\ phase[i] = "trying"
    /\ \A j \in 1..N : (phase[j] # "inCS") \/ (ticket[j] > ticket[i])
    /\ phase' = [phase EXCEPT ![i] = "inCS"]
    /\ UNCHANGED <<ticket, clock>>

Exit(i) ==
    /\ phase[i] = "inCS"
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket, clock>>

Tick ==
    /\ clock' = (clock + 1) % MaxNat
    /\ UNCHANGED <<phase, ticket>>

Next ==
    \/ \E i \in 1..N : Begin(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ Tick

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (phase[i] = "inCS" /\ phase[j] = "inCS") => i = j

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A i \in 1..N : ticket[i] <= MaxNat

====