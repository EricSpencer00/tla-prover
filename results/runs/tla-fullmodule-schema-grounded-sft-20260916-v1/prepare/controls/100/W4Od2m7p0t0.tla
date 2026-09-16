---- MODULE W4Od2m7p0t0 ----
EXTENDS Integers, FiniteSets

Robots == {"r1", "r2", "r3"}
NONE == "none"

VARIABLES reg, inCS, crashed, served

vars == <<reg, inCS, crashed, served>>

Init ==
    /\ reg = NONE
    /\ inCS = NONE
    /\ crashed = {}
    /\ served = {}

TryCAS(r) ==
    /\ r \notin crashed
    /\ reg = NONE
    /\ reg' = r
    /\ UNCHANGED <<inCS, crashed, served>>

Enter(r) ==
    /\ r \notin crashed
    /\ reg = r
    /\ inCS = NONE
    /\ inCS' = r
    /\ UNCHANGED <<reg, crashed, served>>

Exit(r) ==
    /\ r \notin crashed
    /\ inCS = r
    /\ inCS' = NONE
    /\ reg' = NONE
    /\ served' = served \cup {r}
    /\ UNCHANGED crashed

Crash(r) ==
    /\ r \notin crashed
    /\ crashed' = crashed \cup {r}
    /\ UNCHANGED <<reg, inCS, served>>

Idle ==
    /\ \E r \in Robots : r \in crashed
    /\ UNCHANGED vars

Next ==
    \/ \E r \in Robots : TryCAS(r)
    \/ \E r \in Robots : Enter(r)
    \/ \E r \in Robots : Exit(r)
    \/ \E r \in Robots : Crash(r)
    \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ reg \in Robots \cup {NONE}
    /\ inCS \in Robots \cup {NONE}
    /\ crashed \subseteq Robots
    /\ served \subseteq Robots

MutexCoherent ==
    inCS # NONE => reg = inCS

====