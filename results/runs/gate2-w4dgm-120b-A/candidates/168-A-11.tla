---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Requests == (Actors \X {"read", "write"}) \cup {<<0, "none">>}
Actors == 1..NumActors

InQueue(a) == \E i \in DOMAIN queue : queue[i].actor = a

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Requests)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(ProcessQueue)
    /\ WF_vars(Stop)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(a) ==
    /\ ~InQueue(a)
    /\ queue' = Append(queue, <<a, "read">>)
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ ~InQueue(a)
    /\ queue' = Append(queue, <<a, "write">>)
    /\ UNCHANGED <<reading, writing>>

ProcessQueue ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET req == Head(queue) IN
         /\ IF req.actor \in reading \cup writing THEN queue' = Tail(queue) /\ UNCHANGED <<reading, writing>>
            ELSE IF req.op = "read" THEN
                 /\ reading' = reading \cup {req.actor}
                 /\ queue' = Tail(queue)
                 /\ UNCHANGED writing
                 ELSE IF reading = {} THEN
                      /\ writing' = writing \cup {req.actor}
                      /\ queue' = Tail(queue)
                      /\ UNCHANGED reading
                 ELSE
                      /\ queue' = Tail(queue)
                      /\ UNCHANGED <<reading, writing>>
       /\ UNCHANGED <<reading, writing>>

Stop(a ==
    \/ (a \in reading /\ reading' = reading \ {a} /\ UNCHANGED <<writing, queue>>)
    \/ (a \in writing /\ writing' = writing \ {a} /\ UNCHANGED <<reading, queue>>)
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in Actors : Stop(a)

Safety ==
    /\ (writing # {} => reading = {})
    /\ (reading # {} => writing = {})
    /\ Cardinality(writing) <= 1

Liveness ==
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

n == NumActors
====