---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 1

Actors == 1..NumActors

REQUESTS == [type : {"read", "write"}, pid : Actors]

VARIABLES reading, writing, rqQueue

vars == <<reading, writing, rqQueue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ rqQueue \in Seq(REQUESTS)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ rqQueue = <<>>

RequestRead(p) ==
    /\ \A i \in DOMAIN rqQueue : ~(rqQueue[i].pid = p /\ rqQueue[i].type = "read")
    /\ rqQueue' = Append(rqQueue, [type |-> "read", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
    /\ \A i \in DOMAIN rqQueue : ~(rqQueue[i].pid = p /\ rqQueue[i].type = "write")
    /\ rqQueue' = Append(rqQueue, [type |-> "write", pid |-> p])
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ rqQueue # <<>>
    /\ writing = {}
    /\ LET h == Head(rqQueue) IN
        /\ (h.type = "read" \/ (h.type = "write" /\ reading = {}))
        /\ reading' = IF h.type = "read" THEN reading \cup {h.pid} ELSE reading
        /\ writing' = IF h.type = "write" THEN writing \cup {h.pid} ELSE writing
    /\ rqQueue' = Tail(rqQueue)

StopActivity(p) ==
    /\ (p \in reading \/ p \in writing)
    /\ reading' = reading \ {p}
    /\ writing' = writing \ {p}
    /\ UNCHANGED rqQueue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(\E p \in Actors : RequestRead(p))
    /\ SF_vars(\E p \in Actors : RequestWrite(p))
    /\ SF_vars(ProcessQueue)
    /\ SF_vars(\E p \in Actors : StopActivity(p))

Safety ==
    /\ reading # {} => writing = {}
    /\ writing # {} => reading = {}
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ (\A p \in Actors : <>(p \in reading) /\ <>(p \in writing))
    /\ (\A p \in Actors : <>(p \notin reading) /\ <>(p \notin writing))

====