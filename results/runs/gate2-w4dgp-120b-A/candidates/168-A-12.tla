---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

Req == [actor : Actors, kind : {"read", "write"}]

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq(Req)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

\* A process requests read access and joins the end of the queue.
RequestRead(a) ==
    /\ \A k \in DOMAIN queue : queue[k].actor # a
    /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
    /\ UNCHANGED <<reading, writing>>

\* A process requests write access and joins the end of the queue.
RequestWrite(a) ==
    /\ \A k \in DOMAIN queue : queue[k].actor # a
    /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* The process at the front of the queue begins its access, but only if it
\* can coexist with whatever is currently active (writers need exclusive access).
BeginAccess ==
    /\ queue # <<>>
    /\ writing = {}
    /\ LET r == Head(queue) IN
        /\ IF r.kind = "read" THEN
            /\ reading' = reading \cup {r.actor}
            /\ UNCHANGED writing
           ELSE /\ writing' = writing \cup {r.actor}
                /\ UNCHANGED reading
        /\ queue' = Tail(queue)

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
    /\ \A a \in Actors : WF_vars(RequestRead(a))
    /\ \A a \in Actors : WF_vars(RequestWrite(a))
    /\ WF_vars(BeginAccess)
    /\ \A a \in Actors : WF_vars(StopActivity(a))

\* Readers and writers are never both active at once.
Safety ==
    /\ (writing # {} => reading = {})
    /\ \A a \in Actors : (a \in reading \/ a \in writing => reading \cup writing = {a})

\* Every actor eventually reads and eventually writes; no one stays starved.
Liveness ==
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

n == NumActors
====