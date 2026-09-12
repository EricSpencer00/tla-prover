---- MODULE W4Od8m0p3t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Students, Seats, Cap, Nil

VARIABLES seatMap, snapshot, poolCounter, allocation, pending

vars == <<seatMap, snapshot, poolCounter, allocation, pending>>

TypeOK ==
    /\ seatMap \in [Students -> [Seats -> 0, 1]]
    /\ snapshot \in [Students -> 0, 1]
    /\ poolCounter \in 0..Cap
    /\ allocation \in [Seats -> Students \cup {Nil}]
    /\ pending \in Students \cup {Nil}

Init ==
    /\ seatMap = [s \in Students |-> [s' \in Seats |-> 0]]
    /\ snapshot = [s \in Students |-> 0]
    /\ poolCounter = 0
    /\ allocation = [s \in Seats |-> Nil]
    /\ pending = Nil
    /\ TypeOK

Read ==
    /\ seatMap' = seatMap
    /\ snapshot' = [s \in Students |-> (snapshot[s] + 1)]
    /\ pending' = s \in Students : snapshot[s] = snapshot' [s]
    /\ poolCounter' = poolCounter
    /\ allocation' = allocation
    /\ TypeOK

Choose ==
    /\ seatMap' = seatMap
    /\ snapshot' = snapshot
    /\ pending' = s \in Students : snapshot[s] = snapshot' [s] /\ pending = s
    /\ allocation' = [s \in Seats |-> IF s \in pending THEN Nil ELSE allocation[s]]
    /\ TypeOK

Commit ==
    /\ seatMap' = [s \in Students |-> [s' \in Seats |-> IF s' = pending THEN 0 ELSE seatMap[s][s']]]
    /\ snapshot' = snapshot
    /\ pending' = Nil
    /\ allocation' = [s \in Seats |-> IF s = pending THEN pending ELSE allocation[s]]
    /\ IF poolCounter < Cap
        THEN poolCounter' = poolCounter + 1
        ELSE UNCHANGED poolCounter
    /\ TypeOK

Retry ==
    /\ seatMap' = seatMap
    /\ snapshot' = [s \in Students |-> 0]
    /\ pending' = Nil
    /\ allocation' = allocation
    /\ TypeOK

Next ==
    \/ Read
    \/ Choose
    \/ Commit
    \/ Retry

Spec == Init /\ [][Next]_vars

NoDoubleSeat ==
    \A s \in Seats : \E s1, s2 \in Students : s1 # s2 /\ allocation[s] = s1 /\ allocation[s] = s2

====