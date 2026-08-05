---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 3

Actors == 1..NumActors

Requests == [who : Actors, kind : {"read", "write"}]

ActiveWriters(rq) == IF rq.kind = "write" THEN {rq.who} ELSE {}

VARIABLES reading, writing, requests
vars == <<reading, writing, requests>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ requests \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ requests = <<>>

RequestRead(a) ==
    /\ \A i \in 1..Len(requests) : requests[i].who # a /\ requests[i].kind = "write"
    /\ requests' = Append(requests, [who |-> a, kind |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(requests) : requests[i].who # a /\ requests[i].kind = "read"
    /\ requests' = Append(requests, [who |-> a, kind |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginActivity ==
    /\ requests # <<>>
    /\ writing = {}
    /\ LET rq == Head(requests) IN
        /\ IF rq.kind = "read" THEN reading' = reading \cup ActiveWriters(rq) ELSE reading' = reading
        /\ IF rq.kind = "write" /\ reading = {} THEN writing' = writing \cup ActiveWriters(rq) ELSE writing' = writing
        /\ requests' = Tail(requests)

StopActivity(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED requests

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ BeginActivity
    \/ \E a \in Actors : StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(BeginActivity)
    /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
    /\ (writing # {}) => (reading = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A a \in Actors : <>(a \in reading)
    /\ \A a \in Actors : <>(a \in writing)
    /\ \A a \in Actors : [](a \in reading => <>(a \notin reading))
    /\ \A a \in Actors : [](a \in writing => <>(a \notin writing))

====