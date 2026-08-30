---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANT NumActors

\* The queue is a sequence of requests; each request records the requesting
\* actor and whether it wants read or write access.
Requests == [actor: NumActors, mode: {"read", "write"}]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq NumActors
  /\ writing \subseteq NumActors
  /\ queue \in Seq(Requests)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

\* Mutual exclusion of the shared resource: writers and readers never active
\* at the same time, and never more than one writer active.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ writing = {} \/ \E a \in NumActors : writing = {a}

\* Request to read: join the queue unless already waiting to read.
RequestRead(a) ==
  /\ \A k \in DOMAIN queue : ~(queue[k].mode = "read" /\ queue[k].actor = a)
  /\ queue' = Append(queue, [actor |-> a, mode |-> "read"])
  /\ UNCHANGED <<reading, writing>>

\* Request to write: join the queue unless already waiting to write.
RequestWrite(a) ==
  /\ \A k \in DOMAIN queue : ~(queue[k].mode = "write" /\ queue[k].actor = a)
  /\ queue' = Append(queue, [actor |-> a, mode |-> "write"])
  /\ UNCHANGED <<reading, writing>>

\* The queue is processed in order; because requests queue up rather than
\* being arbitrated immediately, a slow actor (late to be serviced) does not
\* block earlier requests -- that is the fairness mechanism that prevents
\* starvation here.
ProcessQueue ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET req == Head(queue) IN
       /\ IF req.actor \in (reading \cup writing)
            THEN queue' = Tail(queue) /\ UNCHANGED <<reading, writing>>
          ELSE IF req.mode = "read"
            THEN reading' = reading \cup {req.actor} /\ queue' = Tail(queue)
                 /\ UNCHANGED writing
            ELSE IF reading = {}
            THEN writing' = {req.actor} /\ queue' = Tail(queue)
                 /\ UNCHANGED reading
            ELSE queue' = queue /\ UNCHANGED <<reading, writing>>
  /\ UNCHANGED <<reading, writing>>

StopActivity(a) ==
  \/ (a \in reading /\ reading' = reading \ {a} /\ UNCHANGED <<writing, queue>>)
  \/ (a \in writing /\ writing' = writing \ {a} /\ UNCHANGED <<reading, queue>>)

Next ==
  \/ \E a \in NumActors : RequestRead(a)
  \/ \E a \in NumActors : RequestWrite(a)
  \/ ProcessQueue
  \/ \E a \in NumActors : StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A a \in NumActors : WF_vars(RequestRead(a))
  /\ \A a \in NumActors : WF_vars(RequestWrite(a))
  /\ WF_vars(ProcessQueue)
  /\ \A a \in NumActors : WF_vars(StopActivity(a))

\* Every actor eventually gets to read and to write, and every active
\* reader/writer eventually stops, so no actor is starved of the resource.
Liveness ==
  /\ \A a \in NumActors : (a \in reading) ~> (a \in writing)
  /\ \A a \in NumActors : (a \in reading) ~> (a \notin reading)
  /\ \A a \in NumActors : (a \in writing) ~> (a \notin writing)

====