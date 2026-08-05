---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

ASSUME NumActors \in Nat /\ NumActors > 0

Actors == 1..NumActors

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

NoOne == 0

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ \A k \in DOMAIN queue : queue[k] \in [who : Actors, kind : {"read", "write"}]

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ queue = <<>>

\* A process that wants to read joins the end of the waiting queue.
RequestRead(p) ==
    /\ \A k \in DOMAIN queue : queue[k].who # p
    /\ queue' = Append(queue, [who |-> p, kind |-> "read"])
    /\ UNCHANGED <<readers, writers>>

\* A process that wants to write joins the end of the waiting queue.
RequestWrite(p) ==
    /\ \A k \in DOMAIN queue : queue[k].who # p
    /\ queue' = Append(queue, [who |-> p, kind |-> "write"])
    /\ UNCHANGED <<readers, writers>>

\* The head of the queue begins reading, or begins writing if no one is reading.
ProcessQueue ==
    /\ queue # <<>>
    /\ writers = {}
    /\ LET front == Head(queue) IN
        /\ IF front.kind = "read"
           THEN readers' = readers \cup {front.who}
           ELSE readers' = readers
        /\ IF front.kind = "write" /\ readers = {}
           THEN writers' = writers \cup {front.who}
           ELSE writers' = writers
        /\ queue' = Tail(queue)
    /\ UNCHANGED readers

StopActivity(p) ==
    /\ \/ p \in readers
       \/ p \in writers
    /\ readers' = readers \ {p}
    /\ writers' = writers \ {p}
    /\ UNCHANGED queue

Next ==
    \/ \E p \in Actors : RequestRead(p)
    \/ \E p \in Actors : RequestWrite(p)
    \/ \E p \in Actors : StopActivity(p)
    \/ ProcessQueue

Spec == Init /\ [][Next]_vars
    /\ WF_vars(ProcessQueue)
    /\ \A p \in Actors :
        /\ WF_vars(\E q \in Actors : RequestRead(q))
        /\ WF_vars(\E q \in Actors : RequestWrite(q))
        /\ WF_vars(StopActivity(p))

Safety == \A p \in Actors :
    /\ (p \in readers => writers = {})
    /\ (p \in writers => readers = {})
    /\ Cardinality(writers) <= 1

\* Every process eventually gets to read.
Liveness == \A p \in Actors :
    /\ (p \in readers) ~> (p \notin readers)
    /\ (p \in writers) ~> (p \notin writers)

====