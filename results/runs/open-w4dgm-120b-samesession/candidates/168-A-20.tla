---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

Actors == 1..NumActors

Mode == {"read", "write"}
Request == [actor: Actors, mode: Mode]

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Request)
    /\ Len(queue) <= NumActors

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ \A i \in 1..Len(queue): queue[i].actor # a \/ queue[i].mode # "read"
    /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in 1..Len(queue): queue[i].actor # a \/ queue[i].mode # "write"
    /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET first == Head(queue) IN
        /\ IF first.mode = "read" THEN reading' = reading \cup {first.actor}
           ELSE IF reading = {} THEN writing' = writing \cup {first.actor}
           ELSE UNCHANGED <<reading, writing>>
        /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors: RequestRead(a)
    \/ \E a \in Actors: RequestWrite(a)
    \/ BeginAccess
    \/ \E a \in Actors: StopActivity(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A a \in Actors: WF_vars(RequestRead(a))
    /\ \A a \in Actors: WF_vars(RequestWrite(a))
    /\ WF_vars(BeginAccess)
    /\ \A a \in Actors: WF_vars(StopActivity(a))

Safety ==
    /\ (writing # {} => reading = {})
    /\ writing \subseteq Actors
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A a \in Actors: (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors: (a \in writing) ~> (a \notin writing)

n == NumActors
====