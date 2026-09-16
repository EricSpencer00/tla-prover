------------------------------ MODULE W4Od14m6p1t5 ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Drones, MaxVer, MaxClock, LeaseLen

NONE == "none"
NoSnap == 99

VARIABLES clock, ver, lease, snap, chain
vars == <<clock, ver, lease, snap, chain>>

LeaseValid(dr) == lease.owner = dr /\ lease.exp > clock

Init ==
    /\ clock = 0
    /\ ver = 0
    /\ lease = [owner |-> NONE, exp |-> 0]
    /\ snap = [dr \in Drones |-> NoSnap]
    /\ chain = << >>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<ver, lease, snap, chain>>

AcquireLease(dr) ==
    /\ lease.exp <= clock
    /\ lease' = [owner |-> dr, exp |-> clock + LeaseLen]
    /\ UNCHANGED <<clock, ver, snap, chain>>

Snapshot(dr) ==
    /\ LeaseValid(dr)
    /\ snap' = [snap EXCEPT ![dr] = ver]
    /\ UNCHANGED <<clock, ver, lease, chain>>

Commit(dr) ==
    /\ LeaseValid(dr)
    /\ snap[dr] = ver
    /\ ver < MaxVer
    /\ ver' = ver + 1
    /\ chain' = Append(chain, ver)
    /\ snap' = [snap EXCEPT ![dr] = NoSnap]
    /\ UNCHANGED <<clock, lease>>

AdminForce ==
    /\ ver < MaxVer
    /\ ver' = ver + 1
    /\ chain' = Append(chain, ver)
    /\ UNCHANGED <<clock, lease, snap>>

Next ==
    \/ Tick
    \/ \E dr \in Drones : AcquireLease(dr)
    \/ \E dr \in Drones : Snapshot(dr)
    \/ \E dr \in Drones : Commit(dr)
    \/ AdminForce

Spec == Init /\ [][Next]_vars

NoLostUpdate ==
    /\ Len(chain) = ver
    /\ \A i \in 1 .. Len(chain) : chain[i] = i - 1

================================================================================