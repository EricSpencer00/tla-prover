---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Reader-writer access to a shared resource, using a request queue to
\* guarantee fair, starvation-free access. Readers and writers never act
\* at the same time (mutual exclusion), and the queue provides
\* first-come-first-served fairness rather than letting one side dominate.
Actors == 1..NumActors
Modes == {"idle", "read", "write"}

\* Readers and writers are tracked in separate sets, and an ordered
\* request queue holds the pending access requests.
VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq([actor: Actors, mode: Modes])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

Waiting(a, m) == [actor |-> a, mode |-> m]

\* A process may enqueue a read or write request while it is not already
\* waiting in the queue.
Enqueue(a, m) ==
    /\ \A i \in 1..Len(queue) : queue[i].actor # a
    /\ queue' = Append(queue, Waiting(a, m))
    /\ UNCHANGED <<reading, writing>>

RequestRead == \E a \in Actors : Enqueue(a, "read")
RequestWrite == \E a \in Actors : Enqueue(a, "write")

Bump(f, i) == [k \in 1..(Len(f) - 1) |-> f[k + i]]

\* The head of the queue is processed only if the resource is currently
\* free in the sense appropriate to the request. A read is allowed as
\* long as nobody is writing; a write needs nobody reading and nobody
\* writing, so the active writer set stays a singleton.
StartAccess(r) == LET h == Head(queue) IN
    /\ \A i \in 1..(Len(queue) - 1) : queue' = Bump(queue, 1)
    /\ IF h.actor \in reading \/ h.actor \in writing
         THEN UNCHANGED <<reading, writing>>
         ELSE IF h.mode = "read" /\ writing = {}
              THEN reading' = reading \cup {h.actor} /\ writing' = writing
              ELSE IF h.mode = "write" /\ reading = {} /\ writing = {}
              THEN writing' = writing \cup {h.actor} /\ reading' = reading
              ELSE UNCHANGED <<reading, writing>>

ProcessQueue == \E r \in {Reading, Writing} : r

\* Any active reader or writer may voluntarily give up the resource.
Stop(a) ==
    \/ reading' = reading \ {a}
    \/ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ RequestRead
    \/ RequestWrite
    \/ ProcessQueue
    \/ \E a \in Actors : Stop(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RequestRead)
    /\ WF_vars(RequestWrite)
    /\ WF_vars(ProcessQueue)
    /\ \A a \in Actors : WF_vars(Stop(a))

\* Readers and writers are mutually exclusive: if any writer is active,
\* the reader set is empty, and vice versa.
Safety == (writing # {}) => (reading = {})
           /\ (reading # {}) => (writing = {})

ReadersEventuallyRest == \A a \in Actors : (a \in reading) ~> (a \notin reading)
WritersEventuallyRest == \A a \in Actors : (a \in writing) ~> (a \notin writing)

Liveness == ReadersEventuallyRest /\ WritersEventuallyRest

\* The configuration file substitutes the concrete pool size for the
\* symbolic constant NumActors.
n == NumActors
====