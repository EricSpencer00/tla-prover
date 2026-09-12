---- MODULE W4Od9m8p4t4 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Feeders, HardCap

VARIABLES
  zoneLock, feederLocks, committedLoad, emergencyCeiling, totalCommittedLoad

vars == <<zoneLock, feederLocks, committedLoad, emergencyCeiling, totalCommittedLoad>>

TypeOK ==
  /\ zoneLock \in {0, 1}
  /\ feederLocks \in [Feeders -> {0, 1}]
  /\ committedLoad \in [Feeders -> 0..HardCap]
  /\ emergencyCeiling \in 0..HardCap
  /\ totalCommittedLoad \in 0..HardCap

Init ==
  /\ zoneLock = 0
  /\ feederLocks = [f \in Feeders |-> 0]
  /\ committedLoad = [f \in Feeders |-> 0]
  /\ emergencyCeiling = 0
  /\ totalCommittedLoad = 0
  /\ TypeOK

Next ==
  /\ zoneLock' = IF emergencyCeiling < totalCommittedLoad \/ totalCommittedLoad > emergencyCeiling
                 THEN IF zoneLock = 1
                      THEN 0
                      ELSE 1
                 ELSE zoneLock
  /\ feederLocks' = [f \in Feeders |-> IF emergencyCeiling < totalCommittedLoad \/ totalCommittedLoad > emergencyCeiling
                                     THEN IF feederLocks[f] = 1
                                          THEN 0
                                          ELSE 1
                                     ELSE feederLocks[f]]
  /\ committedLoad' = [f \in Feeders |-> IF emergencyCeiling < totalCommittedLoad \/ totalCommittedLoad > emergencyCeiling
                                     THEN committedLoad[f]
                                     ELSE committedLoad[f] + 1]
  /\ emergencyCeiling' = emergencyCeiling
  /\ totalCommittedLoad' = \E f \in Feeders : committedLoad'[f]
  /\ TypeOK

Spec == Init /\ [][Next]_vars

CapacityBound == totalCommittedLoad <= HardCap

CeilingRecovers == (emergencyCeiling < totalCommittedLoad) => (zoneLock = 1) /\ (EX i : 1..  \* shedLoadBackDown(i) /\ emergencyCeiling >= totalCommittedLoad)

====