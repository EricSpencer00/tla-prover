---- MODULE W4Od0m9p0t2 ----
EXTENDS Integers
CONSTANTS Rooms, Instances, MaxEpoch
NONE == "none"

VARIABLES avail, occupant, epoch, pending
vars == <<avail, occupant, epoch, pending>>

Init ==
    /\ avail = [r \in Rooms |-> 1]
    occupant = [r \in Rooms |-> NONE]
    /\ epoch = 0
    /\ pending = [i \in Instances |-> {}]

Request(i, r) ==
    /\ r \notin pending[i]
    /\ pending' = [pending EXCEPT ![i] = @ \cup {r}]
    /\ UNCHANGED <<avail, occupant, epoch>>

Acquire(i, r) ==
    /\ r \in pending[i]
    /\ avail[r] = 1
    /\ avail' = [avail EXCEPT ![r] = 0]
    /\ occupant' = [occupant EXCEPT ![r] = i]
    /\ pending' = [pending EXCEPT ![i] = @ \ {r}]
    /\ UNCHANGED epoch

Release(i, r) ==
    /\ occupant[r] = i
    /\ avail' = [avail EXCEPT ![r] = 1]
    /\ occupant' = [occupant EXCEPT ![r] = NONE]
    /\ UNCHANGED <<epoch, pending>>

Reconfigure ==
    /\ epoch < MaxEpoch
    /\ epoch' = epoch + 1
    /\ avail' = [r \in Rooms |-> 1]
    /\ occupant' = [r \in Rooms |-> NONE]
    /\ pending' = [i \in Instances |-> {}]

Next ==
    \/ \E i \in Instances, r \in Rooms : Request(i, r)
    \/ \E i \in Instances, r \in Rooms : Acquire(i, r)
    \/ \E i \in Instances, r \in Rooms : Release(i, r)
    \/ Reconfigure

Spec == Init /\ [][Next]_vars

SemaphoreConsistent ==
    \A r \in Rooms : (avail[r] = 1) <=> (occupant[r] = NONE)
====