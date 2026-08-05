---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Actors == 1..NumActors
Mode == {"read", "write"}
Requests == [who: Actors, mode: Mode]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

RequestRead(a) ==
    /\ \A i \in DOMAIN queue : ~(queue[i].mode = "read" /\ queue[i].who = a)
    /\ queue' = Append(queue, [who |-> a, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ \A i \in DOMAIN queue : ~(queue[i].mode = "write" /\ queue[i].who = a)
    /\ queue' = Append(queue, [who |-> a, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ queue # << >>
    /\ writing = {}
    /\ LET h == Head(queue) IN
        /\ IF h.mode = "read" THEN
            /\ reading' = reading \cup {h.who}
            /\ UNCHANGED writing
        ELSE ( /\ reading = {}
              /\ writing' = writing \cup {h.who}
              /\ UNCHANGED reading )
        /\ queue' = Tail(queue)

StopActivity(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
    \/ ProcessQueue

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A a \in Actors : WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a))
                         /\ WF_vars(ProcessQueue) /\ WF_vars(StopActivity(a))

Safety ==
    /\ (reading # {} => writing = {})
    /\ \A a, b \in writing : a = b

Liveness ==
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====