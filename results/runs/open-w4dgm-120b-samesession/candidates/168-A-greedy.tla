---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* A process is a natural number 1..NumActors; the queue is a sequence of
\* requests, each naming the process and whether it wants to read or write.
Actors == 1..NumActors
Requests == [actor: Actors, kind: {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* A process that is not already waiting to read joins the queue.
RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* A process that is not already waiting to write joins the queue.
RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : queue[i].actor # a
  /\ queue' = Append(queue, [actor |-> a, kind |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed in order; a read may always proceed, a write only
\* when no one is reading, which gives writers a fair chance.
ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ IF r.kind = "read" THEN reading' = reading \cup {r.actor} ELSE
            /\ r.kind = "write"
            /\ reading = {}
            /\ writing' = writing \cup {r.actor}
       /\ queue' = Tail(queue)
  /\ UNCHANGED <<reading, writing>>

StopActivity(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in Actors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ProcessQueue)
  /\ \A a \in Actors : WF_vars(RequestRead(a))
  /\ \A a \in Actors : WF_vars(RequestWrite(a))
  /\ \A a \in Actors : WF_vars(StopActivity(a))

\* Readers and writers are never active at the same time, and at most one
\* writer is ever active.
Safety ==
  /\ (writing # {} => reading = {})
  /\ \A a1, a2 \in writing : a1 = a2

TypeOKInv == TypeOK

\* Every process eventually gets to read and to write, and every active
\* reader/writer eventually stops, so no process is starved.
Liveness ==
  /\ \A a \in Actors : (a \notin reading) ~> (a \in reading)
  /\ \A a \in Actors : (a \notin writing) ~> (a \in writing)
  /\ \A a \in Actors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors : (a \in writing) ~> (a \notin writing)

====