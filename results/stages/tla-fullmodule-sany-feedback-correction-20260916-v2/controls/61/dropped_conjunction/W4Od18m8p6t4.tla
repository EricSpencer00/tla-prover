---- MODULE W4Od18m8p6t4 ----
EXTENDS Naturals, FiniteSets
CONSTANTS Residents, Doors, MaxEpoch
None == "none"
VARIABLES zoneOwner, doorOwner, epoch, cred, capacity
vars == <<zoneOwner, doorOwner, epoch, cred, capacity>>

Locked == {d \in Doors : doorOwner[d] # None}

TypeInv ==
    /\ zoneOwner \in Residents \cup {None}
    doorOwner \in [Doors -> Residents \cup {None}]
    /\ epoch \in 0..MaxEpoch
    /\ cred \in [Residents -> 0..MaxEpoch]
    /\ capacity \in 1..Cardinality(Doors)

Init ==
    /\ zoneOwner = None
    /\ doorOwner = [d \in Doors |-> None]
    /\ epoch = 0
    /\ cred = [p \in Residents |-> 0]
    /\ capacity = Cardinality(Doors)

AcquireZone(p) ==
    /\ zoneOwner = None
    /\ cred[p] = epoch
    /\ zoneOwner' = p
    /\ UNCHANGED <<doorOwner, epoch, cred, capacity>>

ReleaseZone(p) ==
    /\ zoneOwner = p
    /\ \A d \in Doors : doorOwner[d] # p
    /\ zoneOwner' = None
    /\ UNCHANGED <<doorOwner, epoch, cred, capacity>>

LockDoor(p, d) ==
    /\ zoneOwner = p
    /\ cred[p] = epoch
    /\ doorOwner[d] = None
    /\ Cardinality(Locked) < capacity
    /\ doorOwner' = [doorOwner EXCEPT ![d] = p]
    /\ UNCHANGED <<zoneOwner, epoch, cred, capacity>>

UnlockDoor(p, d) ==
    /\ doorOwner[d] = p
    /\ doorOwner' = [doorOwner EXCEPT ![d] = None]
    /\ UNCHANGED <<zoneOwner, epoch, cred, capacity>>

Refresh(p) ==
    /\ cred[p] # epoch
    /\ cred' = [cred EXCEPT ![p] = epoch]
    /\ UNCHANGED <<zoneOwner, doorOwner, epoch, capacity>>

RotateEpoch ==
    /\ epoch < MaxEpoch
    /\ epoch' = epoch + 1
    /\ zoneOwner' = None
    /\ doorOwner' = [d \in Doors |-> None]
    /\ UNCHANGED <<cred, capacity>>

ChangeCapacity ==
    /\ \E c \in 1..Cardinality(Doors) : capacity' = c
    /\ UNCHANGED <<zoneOwner, doorOwner, epoch, cred>>

Next ==
    \/ \E p \in Residents : AcquireZone(p) \/ ReleaseZone(p) \/ Refresh(p)
    \/ \E p \in Residents, d \in Doors : LockDoor(p, d) \/ UnlockDoor(p, d)
    \/ RotateEpoch \/ ChangeCapacity

Spec == Init /\ [][Next]_vars

HierarchyAuthorized ==
    \A d \in Doors :
        doorOwner[d] # None =>
            /\ doorOwner[d] = zoneOwner
            /\ cred[doorOwner[d]] = epoch
====