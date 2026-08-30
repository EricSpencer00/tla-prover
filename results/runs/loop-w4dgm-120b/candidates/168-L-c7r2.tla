---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Readers and writers contend for the shared resource. A bounded queue of
\* access requests (each tagged read/write) is processed first-in-first-out,
\* which is what gives fairness between the two kinds of request and prevents
\* one side from starving the other.
\* Actions are: request read/write, begin access for the head when possible,
\* and stop an active reading or writing process.

\* For model checking the number of actors is finite, chosen by the .cfg.
Actors == 1..NumActors

VARIABLES reading, writing, queue
vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq([actor: Actors, kind: {"read", "write"}])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process requests read access and joins the end of the wait queue.
RequestRead(a) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process requests write access and joins the end of the wait queue.
RequestWrite(a) ==
  /\ \A i \in 1..Len(queue): queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The head of the queue begins its access if the resource is free for it.
BeginAccess ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET h == Head(queue) IN
       /\ \/ (h.kind = "read")
          \/ /\ h.kind = "write"
             /\ reading = {}
          /\ reading' = IF h.kind = "read" THEN reading \cup {h.actor} ELSE reading
          /\ writing' = IF h.kind = "write" THEN writing \cup {h.actor} ELSE writing
          /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ BeginAccess
  \/ \E a \in Actors: StopActivity(a)

Spec == Init /\ [][Next]_vars
          /\ \A a \in Actors: WF_vars(RequestRead(a))
          /\ \A a \in Actors: WF_vars(RequestWrite(a))
          /\ WF_vars(BeginAccess)
          /\ \A a \in Actors: WF_vars(StopActivity(a))

\* Readers and writers are never active at the same time, and at most one
\* writer is active at once.
Safety ==
  /\ ~(reading # {} /\ writing # {})
  /\ \A a1, a2 \in writing: a1 = a2

Liveness ==
  /\ \A a \in Actors: <>(a \in reading)
  /\ \A a \in Actors: <>(a \in writing)
  /\ \A a \in Actors: [](a \in reading => <>(a \notin reading))
  /\ \A a \in Actors: [](a \in writing => <>(a \notin writing))

====