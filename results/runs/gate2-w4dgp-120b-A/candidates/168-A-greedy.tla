---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors
Modes == {"read", "write"}
Requests == [mode : Modes, actor : Actors]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A i \in 1..Len(queue) : queue[i].actor # a \/ queue[i].mode # "read"
    /\ queue' = Append(queue, [mode |-> "read", actor |-> a])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(queue) : queue[i].actor # a \/ queue[i].mode # "write"
    /\ queue' = Append(queue, [mode |-> "write", actor |-> a])
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET front == Head(queue) IN
        /\ IF front.mode = "read" THEN reading' = reading \cup {front.actor} ELSE reading' = reading
        /\ IF front.mode = "write" /\ reading = {} THEN writing' = writing \cup {front.actor} ELSE writing' = writing
        /\ queue' = Tail(queue)
    /\ UNCHANGED reading

StopActivity(a) ==
    /\ (a \in reading \/ a \in writing)
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====