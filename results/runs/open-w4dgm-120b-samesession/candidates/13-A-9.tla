---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES ticket, inCS, mode, started

vars == <<ticket, inCS, mode, started>>

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN ticket[x] + SumOf(S \ {x})

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ mode \in {"idle", "trying", "cs"}
    /\ started \in 0..N

Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ mode = "idle"
    /\ started = 0

StartAttempt ==
    /\ mode = "idle"
    /\ started < N
    /\ mode' = "trying"
    /\ started' = started + 1
    /\ UNCHANGED <<ticket, inCS>>

TakeTicket(i) ==
    /\ mode = "trying"
    /\ ticket[i] = 0
    /\ \A j \in 1..N : ticket[j] # ticket[i]
    /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] = 0 THEN 1 ELSE ticket[i] + 1]
    /\ UNCHANGED <<inCS, mode, started>>

Enter(i) ==
    /\ mode = "trying"
    /\ mode' = "cs"
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, started>>

Exit(i) ==
    /\ mode = "cs"
    /\ mode' = "idle"
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED started

NewAttempt == StartAttempt \/ \E i \in 1..N : TakeTicket(i)

Next == NewAttempt \/ (\E i \in 1..N : Enter(i) \/ Exit(i))

MutualExclusion == SumOf(inCS) <= 1

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars /\ WF_vars(NewAttempt)

====