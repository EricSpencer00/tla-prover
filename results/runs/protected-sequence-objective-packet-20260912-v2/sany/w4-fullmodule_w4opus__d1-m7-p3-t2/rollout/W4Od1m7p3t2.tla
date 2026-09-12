---- MODULE W4Od1m7p3t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Slots, Flights, Instances, Free

VARIABLES alloc, scratch, flightPool, slotOwners, slotHolders

vars == <<alloc, scratch, flightPool, slotOwners, slotHolders>>

TypeOK ==
    /\ alloc \in [Slots -> Flights \cup {Free}]
    /\ scratch \in [Slots -> Flights \cup {Free}]
    /\ flightPool \subseteq Flights
    /\ slotOwners \subseteq [Slots -> Flights \cup {Free}]
    /\ slotHolders \subseteq Flights

Init ==
    /\ alloc = [s \in Slots |-> Free]
    /\ scratch = [s \in Slots |-> Free]
    /\ flightPool = Flights
    /\ slotOwners = [s \in Slots |-> Free]
    /\ slotHolders = {}

Next ==
    /\ UNCHANGED vars \cup {flightPool}
    \/ \E i \in Instances :
        /\ \E j \in Instances : j # i
        /\ \E f \in flightPool : f # slotHolders
        /\ \E s \in Slots : s # scratch[s]
        /\ alloc' = [s \in Slots |-> IF s = s0 THEN f0 ELSE alloc[s]]
        /\ scratch' = [s \in Slots |-> IF s = s0 THEN f0 ELSE scratch[s]]
        /\ flightPool' = flightPool \ {f}
        /\ slotOwners' = [s \in Slots |-> IF s = s0 THEN f0 ELSE slotOwners[s]]
        /\ slotHolders' = slotHolders \cup {f}
        /\ UNCHANGED {alloc, scratch, flightPool, slotOwners, slotHolders} \ {alloc', scratch', flightPool', slotOwners', slotHolders'}

Spec == Init /\ [][Next]_vars

AllocationOK == TypeOK /\ Spec /\ \A s \in Slots : slotOwners[s] = alloc[s] /\ (slotOwners[s] = Free \/ slotHolders = {slotOwners[s]})

====