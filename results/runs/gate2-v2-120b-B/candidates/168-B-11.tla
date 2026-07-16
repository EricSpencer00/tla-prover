---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* processes currently reading
    writers, \* processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

\* Helper to convert a sequence to the corresponding set of its elements
ToSet(s) == { s[i] : i \in DOMAIN s }

\* Predicates to recognise the kind of a request
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

\* Sets of actors waiting for read or write, derived from the queue
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ waiting /= <<>>               \* there must be a request to serve
    /\ Head(waiting)[1] = "read"
    /\ Head(waiting)[2] = actor
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting /= <<>>               \* there must be a request to serve
    /\ Head(waiting)[1] = "write"
    /\ Head(waiting)[2] = actor
    /\ readers = {}                  \* exclusive access
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    \/ \E actor \in Actors : /\ waiting /= <<>> /\ Head(waiting)[1] = "read"  /\ Read(actor)
    \/ \E actor \in Actors : /\ waiting /= <<>> /\ Head(waiting)[1] = "write" /\ Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

\* Stop can be performed by any actor that is currently active
Stop == \E actor \in readers \cup writers : StopActivity(actor)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~ (readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

\* ----------------------------------------------------------------------
\* Liveness (unchanged from original)
\* ----------------------------------------------------------------------
Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

====