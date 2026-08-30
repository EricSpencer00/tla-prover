---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

\* A readers-writers system with a bounded request queue.  Read access may
\* be shared; write access is exclusive.  The bounded queue provides
\* fairness: every waiting request is eventually served in order.
CONSTANTS NumActors

None == "none"
Requests == UNION {[actor |-> a, want |-> w] : a \in NumActors, w \in {"read", "write"}}

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq NumActors
    /\ writing \subseteq NumActors
    /\ queue \in Seq(Requests)

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = <<>>

\* A process asks for read access; it is appended to the tail of the queue.
RequestRead(a) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].actor = a /\ queue[i].want = "read")
    /\ queue' = Append(queue, [actor |-> a, want |-> "read"])
    /\ UNCHANGED <<reading, writing>>

\* A process asks for write access; it is appended to the tail of the queue.
RequestWrite(a) ==
    /\ \A i \in 1..Len(queue) : ~(queue[i].actor = a /\ queue[i].want = "write")
    /\ queue' = Append(queue, [actor |-> a, want |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* The head of the queue is served: a read starts whenever nobody is writing;
\* a write starts only when nobody is reading.
ProcessQueue ==
    /\ queue # <<>>
    /\ LET r == Head(queue) IN
        /\ IF r.want = "read" /\ writing = {}
           THEN reading' = reading \cup {r.actor}
           ELSE IF r.want = "write" /\ reading = {}
               THEN writing' = writing \cup {r.actor}
               ELSE UNCHANGED <<reading, writing>>
        /\ queue' = Tail(queue)

\* A reader or writer voluntarily stops, freeing the shared resource.
StopActivity(a) ==
    /\ (a \in reading \/ a \in writing)
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in NumActors : RequestRead(a)
    \/ \E a \in NumActors : RequestWrite(a)
    \/ ProcessQueue
    \/ \E a \in NumActors : StopActivity(a)

Spec == Init /\ [][Next]_vars
    /\ \A a \in NumActors : WF_vars(RequestRead(a))
    /\ \A a \in NumActors : WF_vars(RequestWrite(a))
    /\ WF_vars(ProcessQueue)
    /\ \A a \in NumActors : WF_vars(StopActivity(a))

\* Safety: readers and writers are never active at the same time.
Safety == (writing # {}) => (reading = {})

\* Liveness: every actor eventually reads and eventually writes.
Liveness == \A a \in NumActors : <>(a \in reading) /\ <>(a \in writing)

\* The .cfg file substitutes a concrete number of actors for the symbolic
\* NumActors constant.  It may also replace NumActors with a small bounded
\* set to keep the model-checking state space finite.
n == NumActors
====