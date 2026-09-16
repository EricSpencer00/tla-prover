---- MODULE W4Od4m1p1t5 ----
EXTENDS Integers, FiniteSets

Stations == {"s1", "s2", "s3"}
Actors == {"s1", "s2", "s3", "admin"}
NONE == "none"
MaxVer == 3

NextSt == [s1 |-> "s2", s2 |-> "s3", s3 |-> "s1"]

VARIABLES version, history, holder, transit

vars == <<version, history, holder, transit>>

Init ==
    /\ version = 0
    /\ history = {}
    /\ holder = "s1"
    /\ transit = NONE

PassToken ==
    /\ holder # NONE
    /\ transit = NONE
    /\ transit' = NextSt[holder]
    /\ holder' = NONE
    /\ UNCHANGED <<version, history>>

DeliverToken ==
    /\ transit # NONE
    /\ holder = NONE
    /\ holder' = transit
    /\ transit' = NONE
    /\ UNCHANGED <<version, history>>

Update ==
    /\ holder # NONE
    /\ version < MaxVer
    /\ version' = version + 1
    /\ history' = history \cup {[ver |-> version + 1, writer |-> holder]}
    /\ UNCHANGED <<holder, transit>>

AdminOverride ==
    /\ version < MaxVer
    /\ version' = version + 1
    /\ history' = history \cup {[ver |-> version + 1, writer |-> "admin"]}
    /\ UNCHANGED <<holder, transit>>

Next ==
    \/ PassToken
    \/ DeliverToken
    \/ Update
    \/ AdminOverride

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ version \in 0..MaxVer
    /\ history \subseteq [ver : 1..MaxVer, writer : Actors]
    /\ holder \in Stations \cup {NONE}
    /\ transit \in Stations \cup {NONE}

HistoryContiguous ==
    {r.ver : r \in history} = (1..version)

====