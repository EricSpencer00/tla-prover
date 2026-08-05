---- MODULE ReadersWriters ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NumActors

\* Readers and writers contend for one shared resource with FCFS fairness:
\* access requests (read or write) enter an ordered queue, and the process at
\* the front is granted the resource when its request is compatible with the
\* current readers/writer. Because no request is skipped, a process waiting
\* behind another one is never starved out of order.
Actors == 1..NumActors

VARIABLES readers, writers, queue

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ queue \in Seq([type : {"read","write"}, pid : Actors])

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

RequestRead(p) ==
    /\ p \notin { q.pid : q \in queue }
    /\ queue' = Append(queue, [type |-> "read", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

RequestWrite(p) ==
    /\ p \notin { q.pid : q \in queue }
    /\ queue' = Append(queue, [type |-> "write", pid |-> p])
    /\ UNCHANGED <<readers, writers>>

\* The head of the queue is granted only if it does not conflict with the
\* current active set; otherwise it stays queued until the resource is free.
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET front == Head(queue) IN
         /\ IF front.type = "read" THEN readers' = readers \cup {front.pid} /\ writers' = writers
            ELSE IF readers = {} THEN readers' = readers /\ writers' = writers \cup {front.pid}
                 ELSE readers' = readers /\ writers' = writers
         /\ queue' = Tail(queue)

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ ProcessQueue
    \/ \E p \in Actors : StopActivity(p)

Spec ==
    /\ Init
    /\ [][Next]_<<readers, writers, queue>>
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actors :
         /\ WF_vars(StopActivity(p))
         /\ WF_vars(RequestRead(p))
         /\ WF_vars(RequestWrite(p))

\* Readers and writers are mutually exclusive, and writers are serialized.
Safety == (writers # {}) => (readers = {}) /\ (Cardinality(writers) <= 1)

Liveness ==
    /\ \A p \in Actors : <> (p \in readers)
    /\ \A p \in Actors : <> (p \in writers)
    /\ \A p \in Actors : (p \in readers) ~> (p \notin readers)
    /\ \A p \in Actors : (p \in writers) ~> (p \notin writers)

====