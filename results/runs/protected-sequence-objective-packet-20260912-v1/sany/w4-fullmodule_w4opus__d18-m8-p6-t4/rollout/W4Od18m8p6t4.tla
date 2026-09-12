---- MODULE W4Od18m8p6t4 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Residents, Doors, MaxEpoch

VARIABLES zone, epoch, credential, doorLocks, zoneOwner, liveCapacity

vars == <<zone, epoch, credential, doorLocks, zoneOwner, liveCapacity>>

TypeOK ==
    /\ zone \in Residents
    /\ epoch \in 0..MaxEpoch
    /\ credential \in 0..MaxEpoch
    /\ doorLocks \in [Residents -> SUBSET Doors]
    /\ zoneOwner \in Residents
    /\ liveCapacity \in 0..MaxEpoch

Init ==
    /\ zone = CHOOSE r \in Residents : TRUE
    /\ epoch = 0
    /\ credential = 0
    /\ doorLocks = [r' \in Residents |-> {}]
    /\ zoneOwner = r
    /\ liveCapacity = 0

Next ==
    /\ IF epoch < MaxEpoch
        THEN credential' = credential + 1
        ELSE credential' = 0
    /\ epoch' = IF epoch < MaxEpoch THEN epoch + 1 ELSE 0
    /\ UNCHANGED <<zone, doorLocks, zoneOwner, liveCapacity>>

HeldByZoneOwner ==
    \A d \in Doors : (d \in doorLocks[zoneOwner]) /\ credential = epoch

HierarchyAuthorized ==
    /\ (zone \in Residents) /\ credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => (zone = zoneOwner)
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \notin doorLocks[zone]) => (zone \in Residents) /\ credential = epoch
    /\ \A d \in Doors : (d \notin doorLocks[zone]) => credential < epoch
    /\ \A d \in Doors : (d \notin doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \notin doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => zone = zoneOwner
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential < MaxEpoch
    /\ \A d \in Doors : (d \in doorLocks[zone]) => liveCapacity > 0
    /\ \A d \in Doors : (d \in doorLocks[zone]) => credential = epoch
    /\