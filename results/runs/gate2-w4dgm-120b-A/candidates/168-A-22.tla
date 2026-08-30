---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

CONSTANTS NumActors

Actors == 1..NumActors

Requests == [actor : Actors, mode : {"read", "write"}]

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

ReqValid(a) ==
    /\ \A i \in DOMAIN queue : queue[i].actor # a
    /\ Cardinality(reading) < NumActors

RequestRead(a) ==
    /\ ReqValid(a)
    /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ ReqValid(a)
    /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginRW ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET r == Head(queue) IN
        /\ IF r.mode = "read" THEN reading' = reading \cup {r.actor} /\ writing' = writing
           ELSE IF reading = {} THEN reading' = reading /\ writing' = writing \cup {r.actor}
           ELSE reading' = reading /\ writing' = writing
        /\ queue' = Tail(queue)
    /\ UNCHANGED writing

StopActivity(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ BeginRW
    \/ \E a \in Actors : StopActivity(a)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(BeginRW)
    /\ \A a \in Actors : SF_vars(RequestRead(a))
    /\ \A a \in Actors : SF_vars(RequestWrite(a))
    /\ \A a \in Actors : SF_vars(StopActivity(a))

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ \A a1 \in reading, a2 \in reading : a1 = a2 \/ a1 # a2
    /\ \A a1 \in writing, a2 \in writing : a1 = a2

Liveness ==
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

n == NumActors

====