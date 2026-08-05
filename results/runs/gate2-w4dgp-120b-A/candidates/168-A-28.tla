---- MODULE ReadersWriters ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS NumActors

Actors == 1..NumActors

Direction == {"read", "write"}

VARIABLES readers, writers, queue

vars == <<readers, writers, queue>>

\* queue is a first-in-first-out sequence of access requests; each
\* request notes the actor and whether it wants to read or write.
QueueSize == 2

TypeOK ==
  /\ readers \subseteq Actors
  /\ writers \subseteq Actors
  /\ queue \in Seq([who : Actors, dir : Direction])

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = <<>>

\* A process that wants to read joins the back of the queue.
RequestRead(a) ==
  /\ [who |-> a, dir |-> "read"] \notin set queue
  /\ Len(queue) < QueueSize
  /\ queue' = Append(queue, [who |-> a, dir |-> "read"])
  /\ UNCHANGED <<readers, writers>>

\* A process that wants to write joins the back of the queue.
RequestWrite(a) ==
  /\ [who |-> a, dir |-> "write"] \notin set queue
  /\ Len(queue) < QueueSize
  /\ queue' = Append(queue, [who |-> a, dir |-> "write"])
  /\ UNCHANGED <<readers, writers>>

\* The front request is granted when it is safe to do so.
ProcessQueue ==
  /\ queue # <<>>
  /\ writers = {}
  /\ LET r == Head(queue) IN
       /\ IF r.dir = "read"
            THEN readers' = readers \cup {r.who} /\ writers' = writers
            ELSE /\ readers = {}
                 /\ writers' = writers \cup {r.who} /\ readers' = readers
       /\ queue' = Tail(queue)

\* An active reader or writer may voluntarily stop.
StopActivity(a) ==
  /\ \/ a \in readers \/ a \in writers
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : RequestRead(a))
  /\ WF_vars(\E a \in Actors : RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ WF_vars(\E a \in Actors : StopActivity(a))

Safety ==
  /\ \A a \in Actors : ~(a \in readers /\ a \in writers)
  /\ readers = {} \/ writers = {}
  /\ Cardinality(writers) <= 1

Liveness ==
  /\ \A a \in Actors : (a \in readers) ~> (a \notin readers)
  /\ \A a \in Actors : (a \in writers) ~> (a \notin writers)

====