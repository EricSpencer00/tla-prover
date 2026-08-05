---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat

Actors == 1..NumActors

Request == [act: {"read", "write"}, proc: Actors]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Request)

Safety ==
    /\ \A a \in reading : a \notin writing
    /\ \A a \in writing : a \notin reading
    /\ Cardinality(writing) <= 1

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A i \in 1..Len(queue) : queue[i].proc # a
    /\ queue' = Append(queue, [act |-> "read", proc |-> a])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(queue) : queue[i].proc # a
    /\ queue' = Append(queue, [act |-> "write", proc |-> a])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ IF queue[1].act = "read"
       THEN reading' = reading \cup {queue[1].proc}
       ELSE IF reading = {}
            THEN writing' = writing \cup {queue[1].proc}
            ELSE UNCHANGED <<reading, writing>>
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<reading, writing>>

StopActivity(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ BeginAccess
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(BeginAccess)
    /\ \A a \in Actors :
        /\ WF_vars(RequestRead(a))
        /\ WF_vars(RequestWrite(a))
        /\ WF_vars(StopActivity(a))

Liveness ==
    /\ \A a \in Actors : TRUE ~> (a \in reading \/ a \in writing)
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====