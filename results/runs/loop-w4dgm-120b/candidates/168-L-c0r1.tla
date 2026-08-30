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

\* The head of the queue is granted only when it is safe to do so.
Grant ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ IF r.kind = "read"
            THEN reading' = reading \cup {r.actor}
            ELSE IF reading = {}
                 THEN writing' = writing \cup {r.actor}
                 ELSE UNCHANGED writing
            /\ queue' = Tail(queue)
  /\ UNCHANGED <<reading, writing>>

Stop(a) ==
  /\ \/ a \in reading
     \/ a \in writing
  /\ reading' = reading \ {a}
  /\ writing' = writing \ {a}
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors : RequestRead(a)
  \/ \E a \in Actors : RequestWrite(a)
  \/ Grant
  \/ \E a \in Actors : Stop(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Grant)
  /\ \A a \in Actors : WF_vars(RequestRead(a)) /\ WF_vars(RequestWrite(a)) /\ WF_vars(Stop(a))

\* Readers and writers are never active at the same time, and at most one
\* writer is ever active.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ \A a1, a2 \in writing : a1 = a2

\* Every process eventually gets to read and to write.
Liveness ==
  \A a \in Actors : (a \in reading) ~> (a \in writing)

\* The .cfg file substitutes the concrete number of actors for n.
n == NumActors

====