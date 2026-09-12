---- MODULE W4Od14m8p3t1 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Drones, Slots, NONE

VARIABLES
  coarseLocks, fineLocks, slotBindings
  droneHolds, slotHeldBy

vars == << coarseLocks, fineLocks, slotBindings, droneHolds, slotHeldBy >>

TypeOK ==
  /\ coarseLocks \in [Drones -> BOOLEAN]
  /\ fineLocks \in [Drones -> [Drones -> BOOLEAN]]
  /\ slotBindings \in [Slots -> Drones]
  /\ droneHolds \in [Drones -> BOOLEAN]
  /\ slotHeldBy \in [Slots -> Drones]

Init ==
  /\ coarseLocks = [d \in Drones |-> FALSE]
  /\ fineLocks = [d \in Drones |-> [d \in Drones |-> FALSE]]
  /\ slotBindings = [s \in Slots |-> NONE]
  /\ droneHolds = [d \in Drones |-> FALSE]
  /\ slotHeldBy = [s \in Slots |-> NONE]
  /\ TypeOK

Next ==
  /\ coarseLocks' = coarseLocks
  /\ fineLocks' = fineLocks
  /\ \A d \in Drones, s \in Slots :
    (d \in Drones /\ s \in Slots /\ coarseLocks[d] /\ fineLocks[d][d] /\ ~slotBindings[s] = NONE)
    => (slotBindings' = slotBindings \cup {[s |-> d]})
    /\ (droneHolds' = droneHolds \cup {[d |-> TRUE]})
    /\ (slotHeldBy' = slotHeldBy \cup {[s |-> d]})
  /\ \A d \in Drones, s \in Slots :
    (d \in Drones /\ s \in Slots /\ coarseLocks[d] /\ fineLocks[d][d] /\ slotBindings[s] = d)
    => (slotBindings' = slotBindings \cup {[s |-> NONE]})
    /\ (droneHolds' = droneHolds \cup {[d |-> FALSE]})
    /\ (slotHeldBy' = slotHeldBy)
  /\ TypeOK

AllocationCoherent ==
  /\ \A s \in Slots : slotBindings[s] = NONE \/ slotBindings[s] \in Drones
  /\ \A d \in Drones : droneHolds[d] => slotHeldBy[slotBindings[d]] = d
  /\ \A d \in Drones : droneHolds[d] => \A s \in Slots : slotBindings[s] = NONE \/ slotBindings[s] = d
  /\ \A d \in Drones : droneHolds[d] => \A d' \in Drones : d' # d => slotBindings[s] # d'

====