---- MODULE ReadersWriters
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

\* A new request is never added to the queue if that same process is
\* already waiting for the same kind of access.
TryRead(actor) == /\ actor \notin WaitingToRead
                 /\ waiting' = Append(waiting, <<"read", actor>>)
                 /\ UNCHANGED <<readers, writers>>

TryWrite(actor) == /\ actor \notin WaitingToWrite
                  /\ waiting' = Append(waiting, <<"write", actor>>)
                  /\ UNCHANGED <<readers, writers>>

\* The next request in the queue is served, but only when no writer is
\* active.  Readers and writers share one queue, so the head must be checked
\* against the current state before it is applied.
Read(actor) == /\ readers' = readers \union {actor}
               /\ waiting' = Tail(waiting)
               /\ UNCHANGED writers

Write(actor) == /\ readers = {}
                /\ writers' = writers \union {actor}
                /\ waiting' = Tail(waiting)
                /\ UNCHANGED readers

ReadOrWrite == /\ waiting /= <<>>
               /\ writers = {}
               /\ LET pair  == Head(waiting)
                      actor == pair[2]
                  IN IF pair[1] = "read" THEN Read(actor) ELSE Write(actor)

\* A process finishes reading or writing, freeing the resource.  A writer
\* and a reader never stop at the same time, so the turnstile is not split.
StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cap writers : StopActivity(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Spec ==
    /\ Init /\ [][Next]_vars
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====