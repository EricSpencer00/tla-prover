---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket
vars == <<inCS, ticket, nextTicket>>

NatOverride == 0..MaxNat

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN
    /\ ticket \in [1..N -> NatOverride
    /\ nextTicket \in NatOverride

Init ==
    /\ inCS = [i \in 1..N |-> FALSE
    /\ ticket = [i \in 1..N |-> 0
    /\ nextTicket \in NatOverride

Enter(i) ==
    /\ ~inCS[i]
    /\ ticket[i] = 0
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED inCS

EnterCritical(i) ==
    /\ ticket[i] # 0
    /\ \A j \in 1..N : (~inCS[j] \/ ticket[j] >= ticket[i])
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED nextTicket

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : EnterCritical(i)
    \/ \E i \in 1..N : Exit(i)

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
    /\ MutualExclusion
    /\ TypeOK

ISpec == Init /\ [][Next]_vars

====