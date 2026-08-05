---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors >= 1

Actors == 1..NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

\* The waiting queue is a sequence of (read/write request, requesting actor) pairs.
\* QueueCapacity bounds the queue for a finite model; the algorithm itself does
\* not need a bounded queue and would work with an unbounded FIFO.
QueueCapacity == NumActors

TypeOK ==
    /\ reading \in SUBSET Actors
    /\ writing \in SUBSET Actors
    /\ queue \in Seq([type : {"read", "write"}, actor : Actors])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

\* A fresh request is appended only if it is not already sitting in the queue.
NotInQueue(rt, a) == \A k \in 1..Len(queue) : ~(queue[k].type = rt /\ queue[k].actor = a)

RequestRead(a) ==
    /\ NotInQueue("read", a)
    /\ Len(queue) < QueueCapacity
    /\ queue' = Append(queue, [type |-> "read", actor |-> a])
    /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
    /\ NotInQueue("write", a)
    /\ Len(queue) < QueueCapacity
    /\ queue' = Append(queue, [type |-> "write", actor |-> a])
    /\ UNCHANGED <<reading, writing>>

\* Processing respects FCFS order and grants exclusive access to writers.
BeginAccess ==
    /\ queue # << >>
    /\ writing = {}
    /\ LET front == Head(queue) IN
        /\ IF front.type = "read" THEN reading' = reading \cup {front.actor}
           ELSE IF front.type = "write" /\ reading = {} THEN writing' = writing \cup {front.actor}
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
    \/ \E a \in Actors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)
    \/ BeginAccess

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E a \in Actors : RequestRead(a))
    /\ WF_vars(\E a \in Actors : RequestWrite(a))
    /\ WF_vars(BeginAccess)
    /\ \A a \in Actors : WF_vars(StopActivity(a))

\* Readers and writers are never active together; writers are mutually exclusive.
Safety == (reading # {} => writing = {}) /\ (writing # {} => reading = {}) /\ Cardinality(writing) <= 1

ReadingEventually == \A a \in Actors : (a \in reading) ~> (a \notin reading)
WritingEventually == \A a \in Actors : (a \in writing) ~> (a \notin writing)
Liveness == ReadingEventually /\ WritingEventually

====