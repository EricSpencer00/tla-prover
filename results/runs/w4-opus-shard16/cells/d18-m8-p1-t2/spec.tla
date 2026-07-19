-------------------------- MODULE W4Od18m8p1t2 --------------------------
EXTENDS Naturals

CONSTANTS Instances, Rooms, NoOne, NoRoom, MaxVer

VARIABLES
    coarse,     \* holder of the house-wide coarse lock, or NoOne
    fine,       \* fine[r] : holder of room r's fine lock, or NoOne
    version,    \* version[r] : live version of each room record
    lastBase,   \* lastBase[r] : base version the latest write to r used
    snapRoom,   \* snapRoom[i] : the room instance i has snapshotted, or NoRoom
    snapVer     \* snapVer[i] : the version i snapshotted for that room

vars == << coarse, fine, version, lastBase, snapRoom, snapVer >>

TypeOK ==
    /\ coarse \in (Instances \cup {NoOne})
    /\ fine \in [Rooms -> (Instances \cup {NoOne})]
    /\ version \in [Rooms -> 0..MaxVer]
    /\ lastBase \in [Rooms -> 0..MaxVer]
    /\ snapRoom \in [Instances -> (Rooms \cup {NoRoom})]
    /\ snapVer \in [Instances -> 0..MaxVer]

Init ==
    /\ coarse = NoOne
    /\ fine = [r \in Rooms |-> NoOne]
    /\ version = [r \in Rooms |-> 0]
    /\ lastBase = [r \in Rooms |-> 0]
    /\ snapRoom = [i \in Instances |-> NoRoom]
    /\ snapVer = [i \in Instances |-> 0]

AcquireCoarse(i) ==
    /\ coarse = NoOne
    /\ coarse' = i
    /\ UNCHANGED << fine, version, lastBase, snapRoom, snapVer >>

HoldsNoFine(i) == \A r \in Rooms : fine[r] # i

ReleaseCoarse(i) ==
    /\ coarse = i
    /\ HoldsNoFine(i)
    /\ coarse' = NoOne
    /\ UNCHANGED << fine, version, lastBase, snapRoom, snapVer >>

\* Only the coarse-lock holder may take a room's fine lock; it snapshots then.
AcquireFine(i, r) ==
    /\ coarse = i
    /\ fine[r] = NoOne
    /\ fine' = [fine EXCEPT ![r] = i]
    /\ snapRoom' = [snapRoom EXCEPT ![i] = r]
    /\ snapVer' = [snapVer EXCEPT ![i] = version[r]]
    /\ UNCHANGED << coarse, version, lastBase >>

\* Write requires the room's fine lock and a snapshot that is still current.
Write(i, r) ==
    /\ fine[r] = i
    /\ snapRoom[i] = r
    /\ snapVer[i] = version[r]
    /\ version[r] < MaxVer
    /\ version' = [version EXCEPT ![r] = @ + 1]
    /\ lastBase' = [lastBase EXCEPT ![r] = snapVer[i]]
    /\ UNCHANGED << coarse, fine, snapRoom, snapVer >>

ReleaseFine(i, r) ==
    /\ fine[r] = i
    /\ fine' = [fine EXCEPT ![r] = NoOne]
    /\ snapRoom' = [snapRoom EXCEPT ![i] = NoRoom]
    /\ UNCHANGED << coarse, version, lastBase, snapVer >>

Next ==
    \/ \E i \in Instances : AcquireCoarse(i)
    \/ \E i \in Instances : ReleaseCoarse(i)
    \/ \E i \in Instances, r \in Rooms : AcquireFine(i, r)
    \/ \E i \in Instances, r \in Rooms : Write(i, r)
    \/ \E i \in Instances, r \in Rooms : ReleaseFine(i, r)

Spec == Init /\ [][Next]_vars

\* No lost updates: every room's latest write built on its immediate predecessor.
NoLostUpdate ==
    \A r \in Rooms : (version[r] = 0) \/ (lastBase[r] = version[r] - 1)

=============================================================================
