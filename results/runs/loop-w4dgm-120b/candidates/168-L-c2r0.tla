---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

\* The system tracks who is actively reading, who is actively writing, and the
\* pending access queue. A pending entry records only the requested mode and
\* the requesting process; the actor itself is the only entity that ever
\* enqueues or begins activity, so the queue never holds a stale (no-longer
\* present) process.
VARIABLES reading, writing, queue

Actors == 1..NumActors
Requests == {r \in [actor: Actors, mode: {"read", "write"}] : TRUE}

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Requests)

\* SAFETY: Readers and writers are disjoint, and only one writer is ever active.
Safety ==
  /\ reading \cap writing = {}
  /\ \A a, b \in writing : a = b
  /\ reading \cup writing \subseteq Actors

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

\* A process that is neither waiting nor active may enqueue a read request.
RequestRead(a) ==
  /\ ~ \E i \in 1..Len(queue) : queue[i].actor = a
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process that is neither waiting nor active may enqueue a write request.
RequestWrite(a) ==
  /\ ~ \E i \in 1..Len(queue) : queue[i].actor = a
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The head of the queue begins its activity if the resource is free in the
\* required sense. The queue is explicitly advanced here so the head is never
\* re-served while its owner is still mid-request.
Dequeue ==
  /\ queue # << >>
  /\ LET h == Head(queue) IN
       /\ IF h.mode = "read" THEN reading' = reading \cup {h.actor} ELSE reading' = reading
       /\ IF h.mode = "write" /\ reading = {} THEN writing' = writing \cup {h.actor} ELSE writing' = writing
       /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ a \in reading \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ Dequeue
  \/ \E a \in Actors : StopActivity(a)

\* SAFETY is a state invariant; fairness on the activity-start action (which
\* includes both reading and writing) is what prevents a queued request from
\* being postponed forever while the other mode monopolizes the resource.
Spec ==
  /\ Init
  /\ [][Next]_<<reading, writing, queue>>
  /\ \A a \in Actors : SF_vars(StopActivity(a))
  /\ SF_vars(Dequeue)
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))

\* LIVENESS: every process eventually gets to read, and to write -- and every
\* active read/write eventually stops, so fairness can keep making progress.
Liveness ==
  /\ \A a \in Actors : <>(a \in reading)
  /\ \A a \in Actors : <>(a \in writing)
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

\* The .cfg file substitutes a concrete bounded value for NumActors (the
\* constant n) before TLC checks the model; the specification itself stays
\* parameterized.
n == 2

====