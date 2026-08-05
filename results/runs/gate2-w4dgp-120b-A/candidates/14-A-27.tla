---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

Process == 0 .. (N - 1)
MutexFree == N

VARIABLES active, waiting, ticket, maxSeen
vars == << active, waiting, ticket, maxSeen >>

Init ==
    /\ active = MutexFree
    /\ waiting = {}
    /\ ticket = [p \in Process |-> 0]
    /\ maxSeen = 0

Request(p) ==
    /\ active # p
    /\ p \notin waiting
    /\ waiting' = waiting \cup {p}
    /\ UNCHANGED << active, ticket, maxSeen >>

TryAcquire(p) ==
    /\ active = MutexFree
    /\ p \in waiting
    /\ ticket[p] > maxSeen
    /\ active' = p
    /\ waiting' = waiting \ {p}
    /\ maxSeen' = IF ticket[p] > maxSeen THEN ticket[p] ELSE maxSeen
    /\ UNCHANGED ticket

Release(p) ==
    /\ active = p
    /\ active' = MutexFree
    /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < (MaxNat - 1) THEN ticket[p] + 1 ELSE ticket[p]]
    /\ UNCHANGED << waiting, maxSeen >>

Next ==
    \/ \E p \in Process : Request(p)
    \/ \E p \in Process : TryAcquire(p)
    \/ \E p \in Process : Release(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == active = MutexFree \/ \E p \in Process : active = p

TypeOK ==
    /\ active \in Process \cup {MutexFree}
    /\ waiting \subseteq Process
    /\ ticket \in [Process -> 0 .. (MaxNat - 1)]

Inv ==
    /\ maxSeen \in 0 .. (MaxNat - 1)
    /\ \A p \in Process : ticket[p] \in 0 .. (MaxNat - 1)

NatOverride == {0, 1, 2, 3}

StateConstraint == \A p \in Process : ticket[p] < MaxNat

====