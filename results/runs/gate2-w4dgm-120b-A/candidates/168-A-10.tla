---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat

Requests == [process : 0..(NumActors - 1), kind : {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq (0..(NumActors - 1))
    /\ writing \subseteq (0..(NumActors - 1))
    /\ queue \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

RequestRead(i) ==
    /\ \A k \in DOMAIN queue : ~ (queue[k].process = i /\ queue[k].kind = "read")
    /\ queue' = Append(queue, [process |-> i, kind |-> "read"])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(i) ==
    /\ \A k \in DOMAIN queue : ~ (queue[k].process = i /\ queue[k].kind = "write")
    /\ queue' = Append(queue, [process |-> i, kind |-> "write"])
    /\ UNCHANGED <<reading, writing>>

BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET req == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ IF req.kind = "read" THEN
            reading' = reading \cup {req.process}
            /\ writing' = writing
           ELSE
            IF reading = {} THEN
                writing' = writing \cup {req.process}
                /\ reading' = reading
            ELSE
                writing' = writing
                /\ reading' = reading
        /\ UNCHANGED << >>

StopActivity(i) ==
    /\ \/ i \in reading
       \/ i \in writing
    /\ reading' = reading \ {i}
    /\ writing' = writing \ {i}
    /\ UNCHANGED queue

Next ==
    \/ BeginAccess
    \/ \E i \in 0..(NumActors - 1) : RequestRead(i) \/ RequestWrite(i) \/ StopActivity(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(BeginAccess)
    /\ \A i \in 0..(NumActors - 1) : WF_vars(RequestRead(i)) /\ WF_vars(RequestWrite(i)) /\ WF_vars(StopActivity(i))

\* Readers and writers are never active at the same time.
Safety ==
    /\ (reading # {}) => (writing = {})
    /\ (writing # {}) => (reading = {})
    /\ (\A a, b \in writing : a = b)

Liveness ==
    /\ \A i \in 0..(NumActors - 1) : (i \in reading) ~> (i \in writing)
    /\ \A i \in 0..(NumActors - 1) : (i \in writing) ~> (i \in reading)
    /\ \A i \in 0..(NumActors - 1) : (i \in reading) ~> (i \notin reading)
    /\ \A i \in 0..(NumActors - 1) : (i \in writing) ~> (i \notin writing)

\* For model checking, replace the actor count with a concrete bound.
n == 2
====