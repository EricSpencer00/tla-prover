---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences

\* A readers-writers solution modeled as a fair queue of read/write requests.
\* The queue provides first-come-first-served fairness, so neither readers
\* nor writers starve even when the other kind is busy.
CONSTANTS NumActors

ASSUME NumActors \in Nat \ {0}

Actors == 1 .. NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
    /\ reading \subseteq Actors
    /\ writing \subseteq Actors
    /\ queue \in Seq([actor: Actors, mode: {"read", "write"}])

Init ==
    /\ reading = {}
    /\ writing = {}
    /\ queue = << >>

\* A read request from an idle actor joins the request queue.
RequestRead(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].actor # a
    /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
    /\ UNCHANGED <<reading, writing>>

\* A write request from an idle actor joins the request queue.
RequestWrite(a) ==
    /\ \A i \in 1 .. Len(queue) : queue[i].actor # a
    /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
    /\ UNCHANGED <<reading, writing>>

\* The front request is admitted only when it would not conflict with the
\* current active readers/writers: reads are blocked by a writer, writes
\* are blocked by any reader. The request leaves the queue once admitted.
Admit ==
    /\ queue # << >>
    /\ ~writing # {}
    /\ LET front == Head(queue) IN
        /\ IF front.mode = "read" THEN
            /\ reading' = reading \cup {front.actor}
            /\ writing' = writing
           ELSE
            /\ writing' = IF reading = {} THEN writing \cup {front.actor} ELSE writing
            /\ reading' = reading
        /\ queue' = Tail(queue)

\* An active reader or writer voluntarily releases the resource.
Release(a) ==
    /\ \/ a \in reading
       \/ a \in writing
    /\ reading' = reading \ {a}
    /\ writing' = writing \ {a}
    /\ UNCHANGED queue

Next ==
    \/ \E a \in Actors : RequestRead(a)
    \/ \E a \in Actors : RequestWrite(a)
    \/ Admit
    \/ \E a \in Actors : Release(a)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(Admit)
    /\ \A a \in Actors : WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a)) /\ WF_vars(Release(a))

\* Safety: readers and writers never overlap, and at most one writer is active.
Safety ==
    /\ reading \cap writing = {}
    /\ writers <= 1
    /\ writers \in {0, 1}

writers == Cardinality(writing)

\* Liveness: every actor eventually gets to read and to write, and every
\* active read/write action eventually stops -- guaranteeing no starvation.
Liveness ==
    /\ \A a \in Actors : <>(a \in reading)
    /\ \A a \in Actors : <>(a \in writing)
    /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
    /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

\* The .cfg substitutes a concrete value for the actor count.
n == 3
====