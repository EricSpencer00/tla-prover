------------------------------ MODULE W4Od13m4p3t2 ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS JobIds, Columns, Instances, None, QCap

VARIABLES queue, owner, holds, finished

vars == <<queue, owner, holds, finished>>

InQueue(id) == \E k \in 1..Len(queue) : queue[k].id = id

Init ==
    /\ queue = <<>>
    /\ owner = [c \in Columns |-> None]
    /\ holds = [j \in JobIds |-> None]
    /\ finished = {}

Enqueue(id, col, i) ==
    /\ Len(queue) < QCap
    /\ ~InQueue(id)
    /\ holds[id] = None
    /\ id \notin finished
    /\ queue' = Append(queue, [id |-> id, col |-> col])
    /\ UNCHANGED <<owner, holds, finished>>

Allocate(i) ==
    /\ Len(queue) > 0
    /\ LET j == Head(queue) IN
         /\ owner[j.col] = None
         /\ owner' = [owner EXCEPT ![j.col] = j.id]
         /\ holds' = [holds EXCEPT ![j.id] = j.col]
         /\ queue' = Tail(queue)
    /\ UNCHANGED finished

DropHead ==
    /\ Len(queue) > 0
    /\ owner[Head(queue).col] # None
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<owner, holds, finished>>

Finish(id) ==
    /\ holds[id] # None
    /\ owner' = [owner EXCEPT ![holds[id]] = None]
    /\ holds' = [holds EXCEPT ![id] = None]
    /\ finished' = finished \cup {id}
    /\ UNCHANGED queue

Idle ==
    /\ Len(queue) = 0
    /\ \A id \in JobIds : id \in finished
    /\ UNCHANGED vars

Next ==
    \/ \E id \in JobIds, col \in Columns, i \in Instances : Enqueue(id, col, i)
    \/ \E i \in Instances : Allocate(i)
    \/ DropHead
    \/ \E id \in JobIds : Finish(id)
    \/ Idle

Spec == Init /\ [][Next]_vars

NoDoubleAllocation ==
    \A id \in JobIds : holds[id] # None => owner[holds[id]] = id

================================================================================