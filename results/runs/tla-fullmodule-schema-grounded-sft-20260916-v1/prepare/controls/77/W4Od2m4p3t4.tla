------------------------------ MODULE W4Od2m4p3t4 ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Robots, Slots, MaxCap, NONE

VARIABLES queue, assigned, capacity, delivered

vars == <<queue, assigned, capacity, delivered>>

Range(q) == {q[i] : i \in 1..Len(q)}
AssignedSlots == {assigned[r] : r \in Robots} \ {NONE}

TypeOK ==
    /\ queue \in Seq(Slots)
    /\ assigned \in [Robots -> Slots \cup {NONE}]
    /\ capacity \in 0..MaxCap
    /\ delivered \subseteq [robot : Robots, slot : Slots]

Init ==
    /\ queue = <<>>
    /\ assigned = [r \in Robots |-> NONE]
    /\ capacity = 1
    /\ delivered = {}

Enqueue(s) ==
    /\ Len(queue) < capacity
    /\ s \notin Range(queue)
    /\ s \notin AssignedSlots
    /\ queue' = Append(queue, s)
    /\ UNCHANGED <<assigned, capacity, delivered>>

Assign(r) ==
    /\ assigned[r] = NONE
    /\ Len(queue) > 0
    /\ LET s == Head(queue) IN
        /\ \A r2 \in Robots : assigned[r2] # s
        /\ assigned' = [assigned EXCEPT ![r] = s]
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<capacity, delivered>>

Complete(r) ==
    /\ assigned[r] # NONE
    /\ delivered' = delivered \cup {[robot |-> r, slot |-> assigned[r]]}
    /\ assigned' = [assigned EXCEPT ![r] = NONE]
    /\ UNCHANGED <<queue, capacity>>

Retune(n) ==
    /\ n \in Len(queue)..MaxCap
    /\ n # capacity
    /\ capacity' = n
    /\ UNCHANGED <<queue, assigned, delivered>>

Next ==
    \/ \E s \in Slots : Enqueue(s)
    \/ \E r \in Robots : Assign(r)
    \/ \E r \in Robots : Complete(r)
    \/ \E n \in 0..MaxCap : Retune(n)

Spec == Init /\ [][Next]_vars

NoDoublyAssignedSlot ==
    \A r1, r2 \in Robots :
        (assigned[r1] # NONE /\ assigned[r1] = assigned[r2]) => r1 = r2
================================================================================