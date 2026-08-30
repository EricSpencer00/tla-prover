---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES ticket, served, inCS, crashed, started

vars == <<ticket, served, inCS, crashed, started>>

Init ==
    /\ ticket = [p \in 1..N |-> 0]
    /\ served = [p \in 1..N |-> 0]
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ crashed = {}
    /\ started = {}

Request(p) ==
    /\ p \notin started
    /\ p \notin crashed
    /\ started' = started \cup {p}
    /\ UNCHANGED <<ticket, served, inCS, crashed>>

Enter(p) ==
    /\ p \in started
    /\ p \notin crashed
    /\ ~inCS[p]
    /\ \A q \in 1..N : q # p => ~inCS[q]
    /\ \A q \in 1..N : q # p => (served[q] = 0 \/ ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q))
    /\ (served[p] = 0 \/ ticket[p] < MaxNat)
    /\ ticket' = [ticket EXCEPT ![p] = IF served[p] = 0 THEN ticket[p] ELSE ticket[p] + 1]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ served' = [served EXCEPT ![p] = IF served[p] = 0 THEN 1 ELSE served[p] + 1]
    /\ UNCHANGED crashed

Exit(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, served, crashed, started>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, served, started>>

Reclaim(p) ==
    /\ p \in crashed
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, served, crashed, started>>

Idle ==
    /\~\E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p) \/ Crash(p) \/ Reclaim(p)
    /\ UNCHANGED vars

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Crash(p)
    \/ \E p \in 1..N : Reclaim(p)
    \/ Idle

Spec == Init /\ [][Next]_vars
ISpec == Spec

MutualExclusion == \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in [1..N -> 0..(MaxNat + 1)]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ crashed \subseteq 1..N
    /\ started \subseteq 1..N

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A p \in 1..N : inCS[p] => (served[p] = 1 /\ (p \in started /\ p \notin crashed))
    /\ \A p, q \in 1..N :
        (p # q /\ served[p] = 1 /\ served[q] = 1) => (ticket[p] # ticket[q])

====