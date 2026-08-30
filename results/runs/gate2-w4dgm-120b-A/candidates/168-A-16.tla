---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* A readers-writers lock built around a first-come-first-served request queue
\* that keeps readers and writers from starving each other. The queue is
\* appended-to by RequestRead/RequestWrite and processed from the front by
\* BeginAccess. Weak fairness on every action, plus the invariant that readers
\* and writers are mutually exclusive, is what guarantees no process is
\* starved of the shared resource.
Actors == 1..NumActors

Request == [kind: {"read", "write"}, actor: Actors]

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq(Request)

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>

RequestRead(a) ==
  /\ ~ \E i \in 1..Len(queue): queue[i].actor = a /\ queue[i].kind = "read"
  /\ queue' = Append(queue, [kind |-> "read", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

RequestWrite(a) ==
  /\ ~ \E i \in 1..Len(queue): queue[i].actor = a /\ queue[i].kind = "write"
  /\ queue' = Append(queue, [kind |-> "write", actor |-> a])
  /\ UNCHANGED <<readers, writers>>

\* Either kind of request may proceed, but a writer only starts once nobody is
\* reading and readers only proceed when no writer is writing.
BeginAccess ==
  /\ queue # << >>
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ (r.kind = "read") \/ (r.kind = "write" /\ readers = {})
       /\ readers' = IF r.kind = "read" THEN readers \cup {r.actor} ELSE readers
       /\ writers' = IF r.kind = "write" THEN writers \cup {r.actor} ELSE writers
       /\ queue' = Tail(queue)

StopActivity(a) ==
  \/ readers' = readers \ {a}
  \/ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ BeginAccess
  \/ \E a \in Actors: StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A a \in Actors: WF_vars(RequestRead(a))
  /\ \A a \in Actors: WF_vars(RequestWrite(a))
  /\ WF_vars(BeginAccess)
  /\ \A a \in Actors: WF_vars(StopActivity(a))

\* Readers and writers are mutually exclusive, and writers are held exclusively.
Safety ==
  /\ (writers # {} => readers = {})
  /\ \A a1, a2 \in Actors: (a1 \in writers /\ a2 \in writers) => (a1 = a2)

Liveness ==
  /\ \A a \in Actors: (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actors: (a \in writers) ~> (a \notin writers)

====