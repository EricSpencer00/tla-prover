-------------------------- MODULE W4Od14m7p2t4 --------------------------
EXTENDS Naturals

CONSTANTS Pilots, Fleet, MaxCap, MaxStamp

VARIABLES
    depot,      \* drones at the ground depot
    perimeter,  \* drones out on the fire perimeter
    stamp,      \* rotating stamp in the compare-and-swap register
    capacity,   \* runtime perimeter capacity
    snapCount,  \* snapCount[p] : perimeter count pilot p snapshotted
    snapStamp,  \* snapStamp[p] : stamp pilot p snapshotted
    armed       \* armed[p] : has p a fresh snapshot it may act on?

vars == << depot, perimeter, stamp, capacity, snapCount, snapStamp, armed >>

TypeOK ==
    /\ depot \in 0..Fleet
    /\ perimeter \in 0..Fleet
    /\ stamp \in 0..MaxStamp
    /\ capacity \in 0..MaxCap
    /\ snapCount \in [Pilots -> 0..Fleet]
    /\ snapStamp \in [Pilots -> 0..MaxStamp]
    /\ armed \in [Pilots -> BOOLEAN]

Init ==
    /\ depot = Fleet
    /\ perimeter = 0
    /\ stamp = 0
    /\ capacity = 1
    /\ snapCount = [p \in Pilots |-> 0]
    /\ snapStamp = [p \in Pilots |-> 0]
    /\ armed = [p \in Pilots |-> FALSE]

NextStamp == IF stamp < MaxStamp THEN stamp + 1 ELSE 0

\* A pilot snapshots the register before attempting a transfer.
Snapshot(p) ==
    /\ snapCount' = [snapCount EXCEPT ![p] = perimeter]
    /\ snapStamp' = [snapStamp EXCEPT ![p] = stamp]
    /\ armed' = [armed EXCEPT ![p] = TRUE]
    /\ UNCHANGED << depot, perimeter, stamp, capacity >>

RegisterMatches(p) == snapCount[p] = perimeter /\ snapStamp[p] = stamp

\* Launch commits only on a matching register, room, and a depot drone.
Launch(p) ==
    /\ armed[p]
    /\ RegisterMatches(p)
    /\ perimeter < capacity
    /\ depot > 0
    /\ depot' = depot - 1
    /\ perimeter' = perimeter + 1
    /\ stamp' = NextStamp
    /\ armed' = [armed EXCEPT ![p] = FALSE]
    /\ UNCHANGED << capacity, snapCount, snapStamp >>

\* Recall commits symmetrically, moving a drone back to the depot.
Recall(p) ==
    /\ armed[p]
    /\ RegisterMatches(p)
    /\ perimeter > 0
    /\ depot' = depot + 1
    /\ perimeter' = perimeter - 1
    /\ stamp' = NextStamp
    /\ armed' = [armed EXCEPT ![p] = FALSE]
    /\ UNCHANGED << capacity, snapCount, snapStamp >>

\* A stale attempt fails; the pilot must re-snapshot.
FailAttempt(p) ==
    /\ armed[p]
    /\ ~RegisterMatches(p)
    /\ armed' = [armed EXCEPT ![p] = FALSE]
    /\ UNCHANGED << depot, perimeter, stamp, capacity, snapCount, snapStamp >>

\* Operations raise the perimeter capacity in calm conditions.
RaiseCap ==
    /\ capacity < MaxCap
    /\ capacity' = capacity + 1
    /\ UNCHANGED << depot, perimeter, stamp, snapCount, snapStamp, armed >>

\* Winds pick up: lower capacity, never below current deployment.
LowerCap ==
    /\ capacity > perimeter
    /\ capacity' = capacity - 1
    /\ UNCHANGED << depot, perimeter, stamp, snapCount, snapStamp, armed >>

Next ==
    \/ \E p \in Pilots : Snapshot(p)
    \/ \E p \in Pilots : Launch(p)
    \/ \E p \in Pilots : Recall(p)
    \/ \E p \in Pilots : FailAttempt(p)
    \/ RaiseCap
    \/ LowerCap

Spec == Init /\ [][Next]_vars

\* Conservation: the fleet is neither created nor destroyed.
FleetConserved == depot + perimeter = Fleet

=============================================================================
