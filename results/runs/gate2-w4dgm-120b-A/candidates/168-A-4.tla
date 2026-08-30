---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

\* Readers-writers with bounded fairness: access requests queue up and are
\* serviced in order, so no read or write is starved.
Actors == 1..n

Request == [act: {"read", "write"}, who: Actors]

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Actors
  /\ writing \subseteq Actors
  /\ queue \in Seq(Request)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

RequestRead(a) ==
  /\ Len(queue) < n
  /\ ~(\E i \in 1..Len(queue): queue[i].who = a /\ queue[i].act = "read")
  /\ queue' = Append(queue, [act |-> "read", who |-> a])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(a) ==
  /\ Len(queue) < n
  /\ ~(\E i \in 1..Len(queue): queue[i].who = a /\ queue[i].act = "write")
  /\ queue' = Append(queue, [act |-> "write", who |-> a])
  /\ UNCHANGED <<reading, writing>>

\* The queue head begins a read or write, but a write only starts when no
\* reader is active; this is what keeps readers and writers exclusive.
Process ==
  /\ queue # <<>>
  /\ writing = {}
  /\ LET r == Head(queue) IN
       /\ IF r.act = "read" THEN
            /\ reading' = reading \cup {r.who}
            /\ writing' = writing
          ELSE
            /\ IF reading = {} THEN
                 /\ reading' = reading
                 /\ writing' = writing \cup {r.who}
               ELSE
                 /\ reading' = reading
                 /\ writing' = writing
       /\ queue' = Tail(queue)

StopActivity(a) ==
  \/ (a \in reading /\ reading' = reading \ {a} /\ writing' = writing)
  \/ (a \in writing /\ writing' = writing \ {a} /\ reading' = reading)
  /\ UNCHANGED queue

Next ==
  \/ \E a \in Actors: RequestRead(a)
  \/ \E a \in Actors: RequestWrite(a)
  \/ Process
  \/ \E a \in Actors: StopActivity(a)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors: RequestRead(a))
  /\ WF_vars(\E a \in Actors: RequestWrite(a))
  /\ WF_vars(Process)
  /\ WF_vars(\E a \in Actors: StopActivity(a))

\* Safety: readers and writers are mutually exclusive, and at most one writer.
Safety ==
  /\ (reading # {} => writing = {})
  /\ \A a, b \in Actors: (a \in writing /\ b \in writing) => a = b

\* Every actor eventually gets to read and write, despite the queue.
Liveness ==
  /\ \A a \in Actors: (a \notin reading) ~> (a \in reading)
  /\ \A a \in Actors: (a \notin writing) ~> (a \in writing)
  /\ \A a \in Actors: (a \in reading) ~> (a \notin reading)
  /\ \A a \in Actors: (a \in writing) ~> (a \notin writing)

====